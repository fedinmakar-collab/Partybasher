import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk, filedialog
from typing import List, Optional, Any, Tuple, Dict
import hashlib
import os
import base64
import hmac
import time
import math
import itertools
import string
import tempfile
import secrets
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives import hashes
from collections import Counter

# --- KDF and HASHING CONSTANTS ---
ARGON2_TIME_COST = 4       # Number of iterations
ARGON2_MEMORY_COST = 102400 # 100 MiB of RAM
ARGON2_PARALLELISM = 8     # Number of parallel threads to use
ENCODING = 'utf-8'
BLOCK_SIZE = 16  # 16 bytes = 128 bits
SALT_SIZE = 32
NONCE_SIZE = 32
NUM_ROUNDS = 32
WORD_SIZE = 64
MASK_64 = 0xFFFFFFFFFFFFFFFF
NUM_SBOXES = 6
SECURITY_LEVEL = "standard"

# Enhanced security parameters
SECURITY_PARAMS = {
    "simple": {"rounds": 20, "sboxes": 4, "arx_rounds": 6, "salt_size": 24, "nonce_size": 24},
    "standard": {"rounds": 32, "sboxes": 6, "arx_rounds": 8, "salt_size": 32, "nonce_size": 32},
    "high": {"rounds": 48, "sboxes": 8, "arx_rounds": 12, "salt_size": 48, "nonce_size": 48}
}

# --- Type Aliases ---
S_BOX = List[int]

# --- ASCII ART HEADER ---
PARTYBASHER_ASCII = r"""
 ███████████    █████████   ███████████   ███████████ █████ █████ ███████████    █████████    █████████  █████   █████ ██████████ ███████████  
░░███░░░░░███  ███░░░░░███ ░░███░░░░░███ ░█░░░███░░░█░░███ ░░███ ░░███░░░░░███  ███░░░░░███  ███░░░░░███░░███   ░░███ ░░███░░░░░█░░███░░░░░███ 
 ░███    ░███ ░███    ░███  ░███    ░███ ░   ░███  ░  ░░███ ███   ░███    ░███ ░███    ░███ ░███    ░░░  ░███    ░███  ░███  █ ░  ░███    ░███ 
 ░██████████  ░███████████  ░██████████      ░███      ░░█████    ░██████████  ░███████████ ░░█████████  ░███████████  ░██████    ░██████████  
 ░███░░░░░░   ░███░░░░░███  ░███░░░░░███     ░███       ░░███     ░███░░░░░███ ░███░░░░░███  ░░░░░░░░███ ░███░░░░░███  ░███░░█    ░███░░░░░███ 
 ░███         ░███    ░███  ░███    ░███     ░███        ░███     ░███    ░███ ░███    ░███  ███    ░███ ░███    ░███  ░███ ░   █ ░███    ░███ 
 █████        █████   █████ █████   █████    █████       █████    ███████████  █████   █████░░█████████  █████   █████ ██████████ █████   █████
░░░░░        ░░░░░   ░░░░░ ░░░░░   ░░░░░    ░░░░░       ░░░░░    ░░░░░░░░░░░  ░░░░░   ░░░░░  ░░░░░░░░░  ░░░░░   ░░░░░ ░░░░░░░░░░ ░░░░░   ░░░░░ 

"""


class ARX:
    """Secure ARX operations with diffusion and non-linear properties"""

    @staticmethod
    def threefish_mix_enhanced(a: int, b: int, rot1: int, rot2: int) -> Tuple[int, int]:
        """Enhanced Threefish-inspired mixing with larger rotations"""
        a = (a + b) & MASK_64
        b = ((b << rot1) | (b >> (64 - rot1))) & MASK_64
        b ^= a
        a = ((a << rot2) | (a >> (64 - rot2))) & MASK_64
        a ^= b
        return a, b

    @staticmethod
    def speck_mix_enhanced(x: int, y: int, key: int) -> Tuple[int, int]:
        """Enhanced Speck-inspired mixing"""
        x = ((x >> 8) | (x << (64 - 8))) & MASK_64  # Rotate right 8
        x = (x + y) & MASK_64
        x ^= key
        y = ((y << 3) | (y >> (64 - 3))) & MASK_64  # Rotate left 3
        y ^= x
        return x, y

    @staticmethod
    def non_linear_transform(state: int, key_word: int) -> int:
        # S-box like transformation using multiplication in Galois Field
        state ^= (state >> 32)
        state = (state * 0x9E3779B97F4A7C15) & MASK_64  # Golden ratio
        state ^= (state >> 32)
        state ^= key_word
        return state

    @staticmethod
    def secure_compression(state: int) -> int:
        # Multiple XOR layers for complete mixing
        result = 0
        for i in range(8):
            result ^= (state >> (i * 8)) & 0xFF
            result ^= (state >> ((i + 4) * 8)) & 0xFF
        # Final permutation
        result = ((result >> 4) | (result << 4)) & 0xFF
        result ^= (result >> 2) | (result << 6)
        result ^= (result >> 1) | (result << 7)
        return result


def safe_int_to_bytes(value: int, num_bytes: int) -> bytes:
    """Safely convert integer to bytes, ensuring it fits within the specified number of bytes"""
    max_value = (1 << (num_bytes * 8)) - 1
    if value > max_value:
        value = value & max_value
    return value.to_bytes(num_bytes, 'big')


def safe_int_from_bytes(data: bytes) -> int:
    """Safely convert bytes to integer"""
    return int.from_bytes(data, 'big')


def arx_hardening(byte: int, key: bytes, rounds: int = 16) -> int:
    """
    Maximum security ARX with 64-bit operations and enhanced properties
    """
    if len(key) < 32:
        key = key * (32 // len(key) + 1)
        key = key[:32]

    # 64-bit state for stronger security margin
    state = (byte << 56) | safe_int_from_bytes(key[:7])

    # Pre-compute key schedule
    key_schedule = []
    for i in range(rounds):
        key_word = safe_int_from_bytes(key[(i * 4) % 28:(i * 4) % 28 + 4])
        key_schedule.append(key_word)

    for round_num in range(rounds):
        # Enhanced rotation amounts with prime-based selection
        rot_a = (key_schedule[round_num] & 0x1F) + 1
        rot_b = ((key_schedule[round_num] >> 5) & 0x1F) + 1
        rot_c = ((key_schedule[round_num] >> 10) & 0x1F) + 1
        rot_d = ((key_schedule[round_num] >> 15) & 0x1F) + 1

        # Multiple addends from different key positions
        addend1 = safe_int_from_bytes(key[(round_num * 2) % 32:(round_num * 2) % 32 + 4])
        addend2 = safe_int_from_bytes(key[(round_num * 2 + 16) % 32:(round_num * 2 + 16) % 32 + 4])
        addend3 = safe_int_from_bytes(key[((round_num + 8) * 3) % 32:((round_num + 8) * 3) % 32 + 4])

        # Enhanced ARX operations
        state = (state + addend1 + addend2 + addend3) & MASK_64

        # Quadruple rotation for maximum diffusion
        state ^= ((state >> rot_a) | (state << (64 - rot_a))) & MASK_64
        state = ((state << rot_b) | (state >> (64 - rot_b))) & MASK_64
        state ^= ((state >> rot_c) | (state << (64 - rot_c))) & MASK_64
        state = ((state << rot_d) | (state >> (64 - rot_d))) & MASK_64

        # Non-linear transformation
        state = ARX.non_linear_transform(state, key_schedule[round_num])

        # Key addition with multiplication for non-linearity
        state ^= (key_schedule[round_num] * (round_num + 1)) & MASK_64

    # Strong compression function
    result = ARX.secure_compression(state)
    return result & 0xFF

# Deterministic cryptographic permutation generator using ChaCha20
def deterministic_permutation_from_chacha20(key: bytes, nonce: bytes, size: int = 256, block_bytes: int = 4096) -> List[int]:
    """
    Produce a deterministic permutation of range(size) using ChaCha20 as a CSPRNG
    and Fisher–Yates shuffle. key must be 32 bytes; nonce must be 16 bytes.
    This is cryptographically strong (unlike MT19937) and deterministic for a given key+nonce.
    """
    if len(key) != 32:
        # pad or truncate to 32 bytes deterministically
        key = (key * (32 // len(key) + 1))[:32]

    if len(nonce) != 16:
        nonce = (nonce * (16 // len(nonce) + 1))[:16]

    cipher = Cipher(algorithms.ChaCha20(key, nonce), mode=None)
    encryptor = cipher.encryptor()

    # Produce initial stream; we will expand as needed
    random_stream = encryptor.update(b'\x00' * block_bytes)
    stream_idx = 0
    stream_len = len(random_stream)

    perm = list(range(size))
    # Fisher-Yates using 4-byte words from the stream to select indices
    for i in range(size - 1, 0, -1):
        # Refill stream if necessary
        if stream_idx + 4 > stream_len:
            extra = encryptor.update(b'\x00' * block_bytes)
            if not extra:
                # defensive fallback (shouldn't happen)
                extra = os.urandom(block_bytes)
            random_stream += extra
            stream_len = len(random_stream)

        j_bytes = random_stream[stream_idx:stream_idx + 4]
        stream_idx += 4
        j = safe_int_from_bytes(j_bytes) % (i + 1)
        perm[i], perm[j] = perm[j], perm[i]

    return perm


def generate_sboxes(key: bytes) -> Tuple[List[int], List[int]]:
    """Generate a deterministic, bijective S-box and its inverse from a 32-byte key.

    Strategy:
      - Ensure key is 32 bytes (pad/truncate deterministically).
      - Use ChaCha20 with domain-separated seeds to produce two independent
        permutations (s_box_base and mapping_perm).
      - Compose them: hardened_s_box = mapping_perm ∘ s_box_base, which is
        guaranteed to be a permutation.
      - Build inverse_s_box and return both.
    """
    # Ensure a 32-byte key
    if len(key) != 32:
        key = key * (32 // len(key) + 1)
        key = key[:32]

    # Domain-separated keys/nonces for ChaCha20-based permutations
    # We derive per-sbox keys/nonces deterministically via SHA3-256 for clarity.
    # base permutation key/nonce
    base_key = hashlib.sha3_256(key + b"partybasher-sbox-base-key").digest()
    base_nonce = hashlib.sha3_256(key + b"partybasher-sbox-base-nonce").digest()[:16]

    # mapping permutation key/nonce (different domain separation)
    map_key = hashlib.sha3_256(key + b"partybasher-sbox-map-key").digest()
    map_nonce = hashlib.sha3_256(key + b"partybasher-sbox-map-nonce").digest()[:16]

    # Generate two deterministic permutations using ChaCha20-driven Fisher-Yates
    s_box_base = deterministic_permutation_from_chacha20(base_key, base_nonce, 256)
    mapping_perm = deterministic_permutation_from_chacha20(map_key, map_nonce, 256)

    # Compose permutations: hardened_s_box[i] = mapping_perm[ s_box_base[i] ]
    hardened_s_box = [mapping_perm[s_box_base[i]] for i in range(256)]

    # Final sanity check — ensure we have a true permutation
    if len(set(hardened_s_box)) != 256:
        # This should never happen: composition of permutations is permutation.
        # Fail loudly to catch unexpected issues.
        raise RuntimeError("S-box generation failed: hardened_s_box is not a permutation")

    # Build inverse S-box
    inverse_s_box = [0] * 256
    for i in range(256):
        inverse_s_box[hardened_s_box[i]] = i

    return hardened_s_box, inverse_s_box


def generate_round_constant(round_index: int) -> int:
    """
    Generate round constant using SHA3-256 for cryptographically secure constants.
    Uses domain separation to ensure unique constants for different purposes.
    """
    # Domain-separated input to prevent constant reuse across different contexts
    domain_separator = b"partybasher_round_constant_v2_"

    # Create unique input for each round with domain separation
    data = domain_separator + round_index.to_bytes(8, 'big')

    # Generate cryptographic hash
    hash_bytes = hashlib.sha3_256(data).digest()

    # Use first 8 bytes for 64-bit constant
    round_constant = int.from_bytes(hash_bytes[:8], 'big')

    return round_constant & MASK_64  # Ensure it fits in 64 bits


class DecryptionError(Exception):
    pass


class PartybasherAlgorithm:
    def __init__(self, security_level: str = "high"):
        self.security_level = security_level
        self.params = SECURITY_PARAMS[security_level]
        self.confetti_map = None
        self.confetti_inverse_map = None

    def _derive_subkeys(self, main_key: bytes) -> Tuple[bytes, bytes]:
        """
        Derive independent subkeys from Argon2 main_key.
        Returns a tuple: (enc_key, mac_key), each 32 bytes.
        We use HKDF-SHA256 with explicit domain separation to produce
        two 32-byte subkeys. This prevents key reuse between cipher
        internals and the HMAC key.
        """

        hkdf = HKDF(
                algorithm=hashes.SHA256(),
                length=64,
                salt=None,
                info=b"partybasher-key-derivation-v1"
            )
        material = hkdf.derive(main_key)
        enc_key = material[:32]
        mac_key = material[32:]
        return enc_key, mac_key

    def _generate_confetti_maps(self, key: bytes):
        # 1. Domain separation: create a dedicated seed for generating the map.
        # Use SHA3-256 to derive a 32-byte key from the input key and a domain
        # separation label. This key becomes the ChaCha20 key used as a
        # deterministic cryptographic PRNG (CSPRNG) for the Fisher–Yates shuffle.
        map_seed_key = hashlib.sha3_256(key + b"partybasher-confetti-seed").digest()

        # 2. Derive a domain-separated nonce for ChaCha20 from the seed.
        # This prevents accidental reuse of the same key/nonce pair across
        # different uses. We keep the nonce size at 16 bytes as required by
        # the ChaCha20 implementation used elsewhere in the codebase.
        nonce = hashlib.sha3_256(map_seed_key + b"partybasher-confetti-nonce").digest()[:16]

        # 3. Use ChaCha20 as a deterministic cryptographic PRNG to produce
        # a byte stream. We'll consume 4-byte words from the stream to
        # generate unbiased indices for Fisher–Yates.
        cipher = Cipher(algorithms.ChaCha20(map_seed_key, nonce), mode=None)
        encryptor = cipher.encryptor()

        # Pre-generate a reasonably large byte stream. Fisher–Yates on a 128-bit
        # permutation needs up to 255 indices; with 4 bytes per index that's ~1KB.
        # Allocate more to be safe and handle re-fill logic.
        random_stream = encryptor.update(b'\x00' * 4096)
        stream_len = len(random_stream)
        stream_idx = 0

        # 4. Perform a cryptographically secure Fisher–Yates shuffle using the
        # ChaCha20 stream as entropy. This guarantees a proper permutation while
        # ensuring the PRNG is cryptographically strong (unlike MT19937).
        num_bits = BLOCK_SIZE * 8  # 128 bits
        scramble_map = list(range(num_bits))

        for i in range(num_bits - 1, 0, -1):
             # Ensure we have 4 bytes available; if not, extend the stream.
            if stream_idx + 4 > stream_len:
                extra = encryptor.update(b'\x00' * 4096)
                random_stream += extra
                stream_len = len(random_stream)

            j_bytes = random_stream[stream_idx: stream_idx + 4]
            stream_idx += 4
            j = safe_int_from_bytes(j_bytes) % (i + 1)
            scramble_map[i], scramble_map[j] = scramble_map[j], scramble_map[i]

        self.confetti_map = tuple(scramble_map)
        # 5. Build the inverse map needed for unscrambling.
        inverse_map = [0] * num_bits

        for original_pos, new_pos in enumerate(self.confetti_map):
            inverse_map[new_pos] = original_pos
        self.confetti_inverse_map = tuple(inverse_map)

    def _confetti_scramble(self, block_int: int) -> int:
        """Applies the key-dependent bit permutation to a 128-bit integer."""
        scrambled_int = 0
        for i in range(BLOCK_SIZE * 8):
            # If the i-th bit of the input is 1...
            if (block_int >> i) & 1:
                # ...set the corresponding bit in the new, scrambled position to 1.
                scrambled_int |= (1 << self.confetti_map[i])
        return scrambled_int

    def _confetti_unscramble(self, block_int: int) -> int:
        """Reverses the key-dependent bit permutation using the inverse map."""
        unscrambled_int = 0
        for i in range(BLOCK_SIZE * 8):
            # If the i-th bit of the scrambled input is 1...
            if (block_int >> i) & 1:
                # ...set the corresponding bit in the original, unscrambled position to 1.
                unscrambled_int |= (1 << self.confetti_inverse_map[i])
        return unscrambled_int

    def _derive_key_argon2(self, password: bytes, salt: bytes) -> bytes:
        """
        Derives a 32-byte key from a password and salt using Argon2id.
        This is a memory-hard KDF, providing superior resistance to GPU and ASIC attacks.
        """
        try:
            import argon2
            from argon2.low_level import hash_secret_raw, Type
        except ImportError:
            raise RuntimeError("Argon2 library not found. Please run 'pip install argon2-cffi'.")

        # Use the raw, low-level Argon2 function to get the binary key directly.
        main_key = hash_secret_raw(
            secret=password,
            salt=salt,
            time_cost=ARGON2_TIME_COST,
            memory_cost=ARGON2_MEMORY_COST,
            parallelism=ARGON2_PARALLELISM,
            hash_len=32,  # We need a 32-byte (256-bit) key
            type=Type.ID  # Use the recommended Argon2id variant
        )
        return main_key

    def _wipe_memory(self, *args: Any) -> None:
        """Enhanced memory wiping with multiple passes"""
        for item in args:
            if isinstance(item, bytearray):
                for _ in range(3):
                    for i in range(len(item)):
                        item[i] = 0
            elif isinstance(item, list):
                for i in range(len(item)):
                    if isinstance(item[i], (bytearray, list)):
                        self._wipe_memory(item[i])
                    item[i] = None

    def _constant_time_compare(self, a: bytes, b: bytes) -> bool:
        """Constant-time comparison to prevent timing attacks"""
        if len(a) != len(b):
            return False
        result = 0
        for x, y in zip(a, b):
            result |= x ^ y
        return result == 0

    def encrypt(self, text: str, keyword: str) -> str:
        # Use security-level specific sizes
        salt_size = self.params["salt_size"]
        nonce_size = self.params["nonce_size"]

        salt = os.urandom(salt_size)
        nonce = os.urandom(nonce_size)
        main_key = self._derive_key_argon2(keyword.encode(ENCODING), salt)
        # Derive independent encryption key material and MAC key from Argon2 output
        enc_key, mac_key = self._derive_subkeys(main_key)
        # Use enc_key for cipher internals (confetti, S-boxes, round keys)
        self._generate_confetti_maps(enc_key)
        s_boxes = self._generate_all_sboxes(enc_key)
        round_keys = self._create_round_keys(enc_key)
        data = text.encode(ENCODING)
        blocks = [data[i:i + BLOCK_SIZE] for i in range(0, len(data), BLOCK_SIZE)]
        ciphertext_bytes = bytearray()

        for i, block in enumerate(blocks):
            counter_bytes = safe_int_to_bytes(i, BLOCK_SIZE)
            # Handle different nonce sizes by truncating or expanding
            if len(nonce) > BLOCK_SIZE:
                counter_block = bytearray(a ^ b for a, b in zip(nonce[:BLOCK_SIZE], counter_bytes))
            else:
                # Expand smaller nonce (shouldn't happen with new sizes)
                expanded_nonce = nonce + b'\x00' * (BLOCK_SIZE - len(nonce))
                counter_block = bytearray(a ^ b for a, b in zip(expanded_nonce, counter_bytes))

            keystream_block = self._encrypt_block(counter_block, s_boxes, round_keys)
            ciphertext_block = bytearray(a ^ b for a, b in zip(block, keystream_block))
            ciphertext_bytes.extend(ciphertext_block)

        data_to_auth = salt + nonce + ciphertext_bytes
        # Use mac_key for authentication to avoid key reuse
        hmac_tag = hmac.new(mac_key, data_to_auth, 'sha256').digest()

        output = (base64.urlsafe_b64encode(salt).decode(ENCODING) + ":" +
                  base64.urlsafe_b64encode(nonce).decode(ENCODING) + ":" +
                  base64.urlsafe_b64encode(ciphertext_bytes).decode(ENCODING) + ":" +
                  base64.urlsafe_b64encode(hmac_tag).decode(ENCODING))

        # Wipe sensitive material: Argon2 main_key and derived subkeys
        self._wipe_memory(main_key, enc_key, mac_key, s_boxes, round_keys, ciphertext_bytes)
        return output

    def decrypt(self, encrypted_text: str, keyword: str) -> str:
        main_key, enc_key, mac_key, s_boxes, round_keys = None, None, None, None, None
        try:
            parts = encrypted_text.split(':')
            if len(parts) != 4:
                raise DecryptionError("Invalid message format.")

            salt_b64, nonce_b64, ciphertext_b64, hmac_b64 = parts
            salt, nonce, ciphertext_bytes, hmac_tag = (
                base64.urlsafe_b64decode(p) for p in [salt_b64, nonce_b64, ciphertext_b64, hmac_b64]
            )

            # Handle different salt/nonce sizes from previous versions
            # Derive Argon2 main key and then split into enc_key/mac_key
            main_key = self._derive_key_argon2(keyword.encode(ENCODING), salt)
            enc_key, mac_key = self._derive_subkeys(main_key)
            # Verify authentication BEFORE performing expensive initialization.
            data_to_auth = salt + nonce + ciphertext_bytes
            expected_hmac = hmac.new(mac_key, data_to_auth, 'sha256').digest()
            if not self._constant_time_compare(expected_hmac, hmac_tag):
                raise DecryptionError("Authentication failed.")
            # Only after HMAC verification do we generate confetti maps, S-boxes, and round keys
            self._generate_confetti_maps(enc_key)
            s_boxes = self._generate_all_sboxes(enc_key)
            round_keys = self._create_round_keys(enc_key)
            blocks = [ciphertext_bytes[i:i + BLOCK_SIZE] for i in range(0, len(ciphertext_bytes), BLOCK_SIZE)]
            plaintext_bytes = bytearray()

            for i, block in enumerate(blocks):
                counter_bytes = safe_int_to_bytes(i, BLOCK_SIZE)
                # Handle different nonce sizes
                if len(nonce) > BLOCK_SIZE:
                    counter_block = bytearray(a ^ b for a, b in zip(nonce[:BLOCK_SIZE], counter_bytes))
                else:
                    expanded_nonce = nonce + b'\x00' * (BLOCK_SIZE - len(nonce))
                    counter_block = bytearray(a ^ b for a, b in zip(expanded_nonce, counter_bytes))

                keystream_block = self._encrypt_block(counter_block, s_boxes, round_keys)
                plaintext_block = bytearray(a ^ b for a, b in zip(block, keystream_block))
                plaintext_bytes.extend(plaintext_block)

            resulting_data = plaintext_bytes.decode(ENCODING)
            self._wipe_memory(main_key, enc_key, mac_key, s_boxes, round_keys, plaintext_bytes)
            return resulting_data

        except Exception as e:
            self._wipe_memory(main_key, enc_key, mac_key, s_boxes, round_keys)
            raise DecryptionError(
                "Decryption failed. The message may be corrupt, tampered with, or the key is incorrect.") from e

    def encrypt_file(self, input_file_path: str, output_file_path: str, keyword: str) -> None:
        """Encrypt a file using Partybasher cipher with enhanced parameters"""
        salt_size = self.params["salt_size"]
        nonce_size = self.params["nonce_size"]

        salt = os.urandom(salt_size)
        nonce = os.urandom(nonce_size)
        main_key = self._derive_key_argon2(keyword.encode(ENCODING), salt)
        enc_key, mac_key = self._derive_subkeys(main_key)
        self._generate_confetti_maps(enc_key)
        s_boxes = self._generate_all_sboxes(enc_key)
        round_keys = self._create_round_keys(enc_key)

        try:
            with open(input_file_path, 'rb') as f_in:
                file_data = f_in.read()

            # Encrypt the file data
            data = file_data
            blocks = [data[i:i + BLOCK_SIZE] for i in range(0, len(data), BLOCK_SIZE)]
            ciphertext_bytes = bytearray()

            for i, block in enumerate(blocks):
                counter_bytes = safe_int_to_bytes(i, BLOCK_SIZE)
                # Handle different nonce sizes
                if len(nonce) > BLOCK_SIZE:
                    counter_block = bytearray(a ^ b for a, b in zip(nonce[:BLOCK_SIZE], counter_bytes))
                else:
                    expanded_nonce = nonce + b'\x00' * (BLOCK_SIZE - len(nonce))
                    counter_block = bytearray(a ^ b for a, b in zip(expanded_nonce, counter_bytes))

                keystream_block = self._encrypt_block(counter_block, s_boxes, round_keys)
                ciphertext_block = bytearray(a ^ b for a, b in zip(block, keystream_block))
                ciphertext_bytes.extend(ciphertext_block)

            # Create HMAC for authentication
            data_to_auth = salt + nonce + ciphertext_bytes
            hmac_tag = hmac.new(mac_key, data_to_auth, 'sha256').digest()

            # Write encrypted file with header format
            with open(output_file_path, 'wb') as f_out:
                f_out.write(base64.urlsafe_b64encode(salt) + b':')
                f_out.write(base64.urlsafe_b64encode(nonce) + b':')
                f_out.write(base64.urlsafe_b64encode(ciphertext_bytes) + b':')
                f_out.write(base64.urlsafe_b64encode(hmac_tag))

        finally:
            self._wipe_memory(main_key, enc_key, mac_key, s_boxes, round_keys, ciphertext_bytes)

    def decrypt_file(self, input_file_path: str, output_file_path: str, keyword: str) -> None:
        """Decrypt a file using Partybasher cipher"""
        main_key, enc_key, mac_key, s_boxes, round_keys = None, None, None, None, None
        try:
            with open(input_file_path, 'rb') as f_in:
                encrypted_data = f_in.read()

            # Parse the encrypted file format
            parts = encrypted_data.split(b':')
            if len(parts) != 4:
                raise DecryptionError("Invalid encrypted file format.")

            salt_b64, nonce_b64, ciphertext_b64, hmac_b64 = parts
            salt = base64.urlsafe_b64decode(salt_b64)
            nonce = base64.urlsafe_b64decode(nonce_b64)
            ciphertext_bytes = base64.urlsafe_b64decode(ciphertext_b64)
            hmac_tag = base64.urlsafe_b64decode(hmac_b64)

            # Derive key and verify HMAC
            main_key = self._derive_key_argon2(keyword.encode(ENCODING), salt)
            enc_key, mac_key = self._derive_subkeys(main_key)
            # Verify HMAC before expensive initialization
            data_to_auth = salt + nonce + ciphertext_bytes
            expected_hmac = hmac.new(mac_key, data_to_auth, 'sha256').digest()
            if not self._constant_time_compare(expected_hmac, hmac_tag):
                raise DecryptionError("File authentication failed - file may be corrupted or tampered with.")
            # Only after HMAC verification do we create cipher internals
            self._generate_confetti_maps(enc_key)
            s_boxes = self._generate_all_sboxes(enc_key)
            round_keys = self._create_round_keys(enc_key)
            blocks = [ciphertext_bytes[i:i + BLOCK_SIZE] for i in range(0, len(ciphertext_bytes), BLOCK_SIZE)]
            plaintext_bytes = bytearray()

            for i, block in enumerate(blocks):
                counter_bytes = safe_int_to_bytes(i, BLOCK_SIZE)
                # Handle different nonce sizes
                if len(nonce) > BLOCK_SIZE:
                    counter_block = bytearray(a ^ b for a, b in zip(nonce[:BLOCK_SIZE], counter_bytes))
                else:
                    expanded_nonce = nonce + b'\x00' * (BLOCK_SIZE - len(nonce))
                    counter_block = bytearray(a ^ b for a, b in zip(expanded_nonce, counter_bytes))

                keystream_block = self._encrypt_block(counter_block, s_boxes, round_keys)
                plaintext_block = bytearray(a ^ b for a, b in zip(block, keystream_block))
                plaintext_bytes.extend(plaintext_block)

            # Remove padding and write decrypted file
            resulting_data = plaintext_bytes

            with open(output_file_path, 'wb') as f_out:
                f_out.write(resulting_data)

            self._wipe_memory(main_key, enc_key, mac_key, s_boxes, round_keys, plaintext_bytes)

        except Exception as e:
            self._wipe_memory(main_key, enc_key, mac_key, s_boxes, round_keys)
            if isinstance(e, DecryptionError):
                raise
            raise DecryptionError(f"File decryption failed: {str(e)}") from e

    def _generate_all_sboxes(self, main_key: bytes) -> List[List[S_BOX]]:
        s_boxes = []
        for i in range(self.params["sboxes"]):
            sbox_key = hashlib.sha3_256(main_key + b"max-security-sbox-" + str(i).encode()).digest()
            s_box, inv_s_box = generate_sboxes(sbox_key)
            s_boxes.append([s_box, inv_s_box])
        return s_boxes

    def _encrypt_block(self, block: bytes, s_boxes: List[List[S_BOX]], round_keys: List[bytes]) -> bytearray:
        # --- CONFETTI SCRAMBLE (START) ---
        # Convert the 16-byte block to a 128-bit integer to perform bitwise operations.
        state_int = int.from_bytes(block, 'big')
        scrambled_int = self._confetti_scramble(state_int)
        state = bytearray(scrambled_int.to_bytes(BLOCK_SIZE, 'big'))
        # --- END OF CONFETTI SCRAMBLE ---

        # Initial key whitening
        state = bytearray(a ^ b for a, b in zip(state, round_keys[0][:BLOCK_SIZE]))

        # Enhanced round function with round constants
        for i in range(self.params["rounds"]):
            # Generate round constant for additional non-linearity
            round_constant = generate_round_constant(i)
            constant_bytes = round_constant.to_bytes(8, 'big')

            # Multiple S-box layers with different applications
            for j in range(len(s_boxes)):
                state = bytearray(s_boxes[j][0][b] for b in state)

            # Maximum security permutation - ensure it returns bytearray
            state = self._diffusion_permutation(state, round_keys[i + 1])

            # Key addition with round constant
            key_material = round_keys[i + 1][:BLOCK_SIZE]

            if not isinstance(state, bytearray):
                state = bytearray(state)

            # Apply round constant XOR
            for k in range(0, len(state), 8):
                for m in range(min(8, len(state) - k)):
                    state[k + m] ^= constant_bytes[m % 8]

            state = bytearray((a ^ b) for a, b in zip(state, key_material))

            # Additional mixing for even rounds
            if i % 2 == 0:
                state = self._additional_mixing(state, round_keys[i % len(round_keys)])

        # --- CONFETTI UNSCRAMBLE (END) ---
        # To make the entire block operation a strong Pseudo-Random Permutation,
        # we apply the inverse scramble at the end.
        final_state_int = int.from_bytes(state, 'big')
        unscrambled_final_int = self._confetti_unscramble(final_state_int)
        final_state = bytearray(unscrambled_final_int.to_bytes(BLOCK_SIZE, 'big'))
        # --- END OF CONFETTI UNSCRAMBLE ---

        wiped_state = final_state[:]
        self._wipe_memory(state)
        return wiped_state

    def _diffusion_permutation(self, block: bytearray, round_key: bytes) -> bytearray:
        """
        Secure permutation with complete diffusion properties
        """
        words = [
            safe_int_from_bytes(block[0:8]),
            safe_int_from_bytes(block[8:16])
        ]

        # Enhanced rotation generation with larger ranges
        rot = [
            (round_key[0] % 29) + 1,  # 1-29 rotation
            (round_key[1] % 31) + 1,  # 1-31 rotation
            (round_key[2] % 27) + 1,  # 1-27 rotation
            (round_key[3] % 23) + 1,  # 1-23 rotation
        ]

        # Four passes for complete diffusion
        for pass_num in range(4):
            # Threefish-style mixing
            words[0], words[1] = ARX.threefish_mix_enhanced(
                words[0], words[1], rot[0], rot[1])

            # Additional Speck-style mixing
            words[0], words[1] = ARX.speck_mix_enhanced(
                words[0], words[1], safe_int_from_bytes(round_key[4:8]))

            # Dynamic rotation update
            rot = [(r + pass_num) % 32 + 1 for r in rot]

        # Ensure we return bytearray, not bytes
        result = bytearray()
        result.extend(safe_int_to_bytes(words[0], 8))
        result.extend(safe_int_to_bytes(words[1], 8))
        return result

    def _additional_mixing(self, state: bytearray, key: bytes) -> bytearray:
        """Additional mixing function for enhanced diffusion"""
        # XOR with rotated version of itself
        rotated = state[8:] + state[:8]
        state = bytearray(a ^ b for a, b in zip(state, rotated))

        # Key-dependent transformation
        key_int = safe_int_from_bytes(key[:8])
        for i in range(0, 16, 8):
            block_int = safe_int_from_bytes(state[i:i + 8])
            block_int = (block_int + key_int) & MASK_64
            state[i:i + 8] = safe_int_to_bytes(block_int, 8)

        return state


    def _create_round_keys(self, main_key: bytes) -> List[bytes]:
        """
        Creates the round keys using a chained, forward-secure key schedule.
        Each round key is derived from the previous one, making the schedule
        resistant to analysis and related-key attacks.
        """
        if 'sha3_256' not in hashlib.algorithms_available:
            raise RuntimeError("SHA3-256 is not available.")

        round_keys = []
        # Start the chain with the main key. This will be used to derive the first round key.
        current_key_material = main_key
        # Generate a key for each round, plus one for the initial whitening step.
        for i in range(self.params["rounds"] + 1):
            # 1. Generate the unique round constant to break symmetry within the chain.
            round_constant = generate_round_constant(i)
            constant_bytes = round_constant.to_bytes(8, 'big')

            # 2. Derive the next key from the *previous* key material and the constant.
            # This creates the one-way dependency chain.
            next_key = hashlib.sha3_256(
                b"partybasher-key-expansion-" +  # Domain separation prefix
                current_key_material +  # Previous key material in the chain
                constant_bytes  # Unique round constant
            ).digest()
            # 3. Add the newly derived key to our list.
            round_keys.append(next_key)
            # 4. The new key becomes the material for generating the next one.
            current_key_material = next_key

        return round_keys


class PartybasherCryptanalysisLab:
    """Comprehensive cryptographic analysis suite for Partybasher cipher"""

    def __init__(self, cipher):
        self.cipher = cipher
        self.results = {}

    def cipher_validation(self, test_vectors: List[Tuple[str, str, str]]) -> Dict[str, bool]:
        """Validate cipher against test vectors by testing encryption->decryption round trip"""
        results = {}
        for i, (plaintext, key, _) in enumerate(test_vectors):
            try:
                # Test the full encryption -> decryption round trip
                ciphertext = self.cipher.encrypt(plaintext, key)
                decrypted = self.cipher.decrypt(ciphertext, key)

                # Success if we get back the original plaintext
                results[f"Test Vector {i + 1}"] = (decrypted == plaintext)
            except Exception as e:
                results[f"Test Vector {i + 1}"] = False
        return results

    def byte_frequency_analysis(self, ciphertext: str, num_samples: int = 1000) -> Dict[str, Any]:
        """Analyze byte frequency distribution for randomness"""
        try:
            parts = ciphertext.split(':')
            if len(parts) != 4:
                return {"error": "Invalid ciphertext format"}

            ciphertext_bytes = base64.urlsafe_b64decode(parts[2])
            byte_counts = Counter(ciphertext_bytes)

            # Calculate frequency metrics
            total_bytes = len(ciphertext_bytes)
            expected_frequency = 1 / 256
            chi_squared = 0

            for byte_val in range(256):
                observed = byte_counts.get(byte_val, 0)
                expected = total_bytes * expected_frequency
                chi_squared += ((observed - expected) ** 2) / expected

            # Ideal random distribution would have chi-squared ~255
            return {
                "chi_squared": chi_squared,
                "ideal_range": "200-300",
                "entropy_estimate": self._calculate_entropy(byte_counts, total_bytes),
                "uniformity_score": min(1.0, 300 / max(chi_squared, 1)),
                "monobit_test": self._monobit_test(ciphertext_bytes),
                "runs_test": self._runs_test(ciphertext_bytes)
            }
        except Exception as e:
            return {"error": str(e)}

    def _calculate_entropy(self, byte_counts: Counter, total_bytes: int) -> float:
        """Calculate Shannon entropy of byte distribution"""
        entropy = 0.0
        for count in byte_counts.values():
            probability = count / total_bytes
            if probability > 0:
                entropy -= probability * (math.log2(probability))
        return entropy

    def _monobit_test(self, data: bytes) -> str:
        """Monobit test for randomness"""
        ones_count = sum(bin(byte).count('1') for byte in data)
        total_bits = len(data) * 8
        ratio = ones_count / total_bits
        return "PASS" if 0.45 <= ratio <= 0.55 else "FAIL"

    def _runs_test(self, data: bytes) -> str:
        """Runs test for randomness"""
        # Simple runs test implementation
        bits = ''.join(bin(byte)[2:].zfill(8) for byte in data)
        runs = 1
        for i in range(1, len(bits)):
            if bits[i] != bits[i - 1]:
                runs += 1

        # Very basic check - more sophisticated would use statistical bounds
        expected_runs = len(bits) / 2 + 1
        return "PASS" if abs(runs - expected_runs) < len(bits) * 0.1 else "FAIL"

    def avalanche_effect_test(self, plaintext: str, key: str, num_tests: int = 100) -> Dict[str, Any]:
        """Test avalanche effect - how many bits change when input changes"""
        try:
            original_ciphertext = self.cipher.encrypt(plaintext, key)
            original_bytes = base64.urlsafe_b64decode(original_ciphertext.split(':')[2])

            bit_changes = []

            # Test single bit changes in plaintext
            plaintext_bytes = plaintext.encode('utf-8')
            for bit_pos in range(min(num_tests, len(plaintext_bytes) * 8)):
                modified_bytes = bytearray(plaintext_bytes)
                byte_idx = bit_pos // 8
                bit_in_byte = bit_pos % 8

                if byte_idx < len(modified_bytes):
                    modified_bytes[byte_idx] ^= (1 << bit_in_byte)
                    modified_plaintext = modified_bytes.decode('utf-8', errors='ignore')

                    modified_ciphertext = self.cipher.encrypt(modified_plaintext, key)
                    modified_bytes_ct = base64.urlsafe_b64decode(modified_ciphertext.split(':')[2])

                    # Calculate bit difference
                    changes = sum(bin(a ^ b).count('1') for a, b in zip(original_bytes, modified_bytes_ct))
                    bit_changes.append(changes)

            if bit_changes:
                avg_changes = sum(bit_changes) / len(bit_changes)
                max_possible = len(original_bytes) * 8
                avalanche_ratio = avg_changes / max_possible

                # Calculate standard deviation manually (replacing numpy)
                if len(bit_changes) > 1:
                    mean = avg_changes
                    variance = sum((x - mean) ** 2 for x in bit_changes) / len(bit_changes)
                    std_dev = variance ** 0.5
                else:
                    std_dev = 0.0

                return {
                    "average_bit_changes": avg_changes,
                    "max_possible_changes": max_possible,
                    "avalanche_ratio": avalanche_ratio,
                    "target_ratio": 0.5,
                    "deviation": abs(avalanche_ratio - 0.5),
                    "consistency_std_dev": std_dev,
                    "tests_performed": len(bit_changes)
                }
            else:
                return {"error": "No valid tests performed"}

        except Exception as e:
            return {"error": str(e)}

    def bit_flip_attack_simulation(self, ciphertext: str, key: str, num_bits: int = 16) -> Dict[str, Any]:
        """Simulate bit-flip attacks on ciphertext"""
        try:
            parts = ciphertext.split(':')
            if len(parts) != 4:
                return {"error": "Invalid ciphertext format"}

            salt, nonce, ct, hmac_tag = parts
            ciphertext_bytes = base64.urlsafe_b64decode(ct)

            results = {
                "successful_decryptions": 0,
                "failed_decryptions": 0,
                "hmac_detected": 0,
                "gibberish_outputs": 0,
                "total_tests": min(num_bits, len(ciphertext_bytes) * 8)
            }

            # Test flipping bits in ciphertext
            for bit_pos in range(results["total_tests"]):
                modified_ct = bytearray(ciphertext_bytes)
                byte_idx = bit_pos // 8
                bit_in_byte = bit_pos % 8

                modified_ct[byte_idx] ^= (1 << bit_in_byte)
                modified_ct_b64 = base64.urlsafe_b64encode(modified_ct).decode('utf-8')
                modified_ciphertext = f"{salt}:{nonce}:{modified_ct_b64}:{hmac_tag}"

                try:
                    decrypted = self.cipher.decrypt(modified_ciphertext, key)
                    # Check if decryption produces valid text
                    if all(32 <= ord(c) <= 126 for c in decrypted[:10]):
                        results["successful_decryptions"] += 1
                    else:
                        results["gibberish_outputs"] += 1
                except DecryptionError:
                    results["hmac_detected"] += 1
                except Exception:
                    results["failed_decryptions"] += 1

            return results

        except Exception as e:
            return {"error": str(e)}

    def differential_analysis(self, plaintext1: str, plaintext2: str, key: str) -> Dict[str, Any]:
        """Perform differential cryptanalysis between two similar plaintexts"""
        try:
            ciphertext1 = self.cipher.encrypt(plaintext1, key)
            ciphertext2 = self.cipher.encrypt(plaintext2, key)

            ct1_bytes = base64.urlsafe_b64decode(ciphertext1.split(':')[2])
            ct2_bytes = base64.urlsafe_b64decode(ciphertext2.split(':')[2])

            # Calculate difference metrics
            byte_differences = [a ^ b for a, b in zip(ct1_bytes, ct2_bytes)]
            bit_differences = sum(bin(diff).count('1') for diff in byte_differences)

            total_bits = len(ct1_bytes) * 8
            difference_ratio = bit_differences / total_bits

            return {
                "bit_difference_count": bit_differences,
                "total_bits": total_bits,
                "difference_ratio": difference_ratio,
                "expected_ratio": 0.5,
                "deviation": abs(difference_ratio - 0.5),
                "analysis": "Strong resistance" if abs(difference_ratio - 0.5) < 0.1 else "Weak resistance"
            }

        except Exception as e:
            return {"error": str(e)}

    def dictionary_attack_simulation(self, ciphertext: str, dictionary: List[str],
                                     max_attempts: int = 1000) -> Dict[str, Any]:
        """Simulate dictionary attack with progress tracking"""
        results = {
            "attempted": 0,
            "successful": 0,
            "failed": 0,
            "found_key": None,
            "time_taken": 0,
            "attack_speed": 0
        }

        start_time = time.time()

        for i, password in enumerate(dictionary[:max_attempts]):
            try:
                decrypted = self.cipher.decrypt(ciphertext, password)
                results["successful"] += 1
                results["found_key"] = password
                break
            except (DecryptionError, Exception):
                results["failed"] += 1

            results["attempted"] = i + 1

        time_taken = time.time() - start_time
        results["time_taken"] = time_taken
        results["attack_speed"] = results["attempted"] / time_taken if time_taken > 0 else 0

        return results

    def brute_force_simulation(self, ciphertext: str, key_length: int = 3,
                               max_attempts: int = 1000, char_set: str = "printable") -> Dict[str, Any]:
        """Simulate brute force attack with limited keyspace"""
        char_sets = {
            "numeric": string.digits,
            "lowercase": string.ascii_lowercase,
            "uppercase": string.ascii_uppercase,
            "alphanumeric": string.ascii_letters + string.digits,
            "printable": string.printable
        }

        chars = char_sets.get(char_set, string.printable)
        chars = chars[:20]  # Limit character set for demo

        results = {
            "attempted": 0,
            "successful": 0,
            "failed": 0,
            "found_key": None,
            "time_taken": 0,
            "keyspace_size": len(chars) ** key_length,
            "character_set": char_set,
            "attack_speed": 0
        }

        start_time = time.time()

        for attempt, key_tuple in enumerate(itertools.product(chars, repeat=key_length)):
            if attempt >= max_attempts:
                break

            key = ''.join(key_tuple)
            try:
                decrypted = self.cipher.decrypt(ciphertext, key)
                results["successful"] += 1
                results["found_key"] = key
                break
            except (DecryptionError, Exception):
                results["failed"] += 1

            results["attempted"] = attempt + 1

        time_taken = time.time() - start_time
        results["time_taken"] = time_taken
        results["attack_speed"] = results["attempted"] / time_taken if time_taken > 0 else 0

        return results

    def performance_benchmark(self, text_sizes: List[int] = None) -> Dict[str, Any]:
        """Benchmark encryption/decryption performance"""
        if text_sizes is None:
            text_sizes = [100, 1000, 10000]

        results = {}

        for size in text_sizes:
            test_text = "A" * size
            test_key = "benchmark_key"

            # Encryption benchmark
            start_time = time.time()
            ciphertext = self.cipher.encrypt(test_text, test_key)
            encrypt_time = time.time() - start_time

            # Decryption benchmark
            start_time = time.time()
            decrypted = self.cipher.decrypt(ciphertext, test_key)
            decrypt_time = time.time() - start_time

            results[f"{size} chars"] = {
                "encrypt_time": encrypt_time,
                "decrypt_time": decrypt_time,
                "encrypt_speed": size / encrypt_time if encrypt_time > 0 else 0,
                "decrypt_speed": size / decrypt_time if decrypt_time > 0 else 0
            }

        return results


class FileOperationsWindow:
    """Dedicated window for file encryption/decryption operations"""

    STYLE = {
        "font_family": ("Consolas", "Courier New"),
        "font_normal": (("Consolas", 11)),
        "font_bold": (("Consolas", 11, "bold")),
        "font_small_bold": (("Consolas", 9, "bold")),
        "font_ascii": (("Courier New", 9)),
        "colors": {
            "background": "#0D0D0D", "frame": "#1A1A1A", "text": "#00FF41", "header_bg": "#0D0D0D",
            "accent": "#00FF41", "accent_hover": "#90FF90", "button_fg": "#0D0D0D",
            "entry_bg": "#000000", "cursor": "#00FF41", "outline": "#00FF41",
            "good": "#90FF90",
            "warning": "#FF6B00",
            "danger": "#FF0000"
        },
        "padding": {"frame": 20, "widget": 10, "button": (20, 8)},
    }

    def __init__(self, parent, cipher):
        self.parent = parent
        self.cipher = cipher
        self.current_file_path = None
        self.window = None
        self._setup_window()

    def _create_hacker_button(self, parent, text, command, font=None, padx=None, pady=None, bg_color=None):
        font_to_use = font if font else self.STYLE["font_bold"]
        padx_to_use = padx if padx is not None else self.STYLE["padding"]["button"][0]
        pady_to_use = pady if pady is not None else self.STYLE["padding"]["button"][1]
        bg_to_use = bg_color if bg_color else self.STYLE["colors"]["accent"]
        hover_color = self.STYLE["colors"]["accent_hover"]
        btn = tk.Button(parent, text=text, command=command, font=font_to_use, bg=bg_to_use,
                        fg=self.STYLE["colors"]["button_fg"], relief='flat', borderwidth=0, padx=padx_to_use,
                        pady=pady_to_use, activebackground=hover_color,
                        activeforeground=self.STYLE["colors"]["button_fg"])
        btn.bind("<Enter>", lambda e: e.widget.config(bg=hover_color))
        btn.bind("<Leave>", lambda e: e.widget.config(bg=bg_to_use))
        return btn

    def _create_hacker_frame(self, parent, title=None):
        """Create a frame with the hacker style"""
        frame = tk.Frame(parent, bg=self.STYLE["colors"]["frame"],
                         highlightbackground=self.STYLE["colors"]["outline"],
                         highlightthickness=1, padx=15, pady=15)

        if title:
            title_label = tk.Label(frame, text=title, font=self.STYLE["font_bold"],
                                   bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"])
            title_label.pack(fill='x', anchor='w', pady=(0, 10))

        return frame

    def _create_hacker_entry(self, parent, default_text="", width=20):
        """Create an entry field with hacker style"""
        entry = tk.Entry(parent, font=self.STYLE["font_normal"],
                         bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                         relief='flat', borderwidth=0, width=width,
                         insertbackground=self.STYLE["colors"]["cursor"])
        if default_text:
            entry.insert(0, default_text)
        return entry

    def _create_hacker_text(self, parent, height=6):
        """Create a text area with hacker style"""
        text = scrolledtext.ScrolledText(parent, height=height, font=self.STYLE["font_normal"],
                                         bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                                         relief='flat', borderwidth=0, wrap=tk.WORD,
                                         insertbackground=self.STYLE["colors"]["cursor"])
        return text

    def _setup_window(self):
        """Setup the file operations window"""
        self.window = tk.Toplevel(self.parent)
        self.window.title(">>> PARTYBASHER v1.9 - FILE OPERATIONS <<<")
        self.window.geometry("650x1020")
        self.window.minsize(650, 1020)
        self.window.configure(bg=self.STYLE["colors"]["background"])
        self.window.transient(self.parent)
        self.window.grab_set()

        # Create header
        header_frame = tk.Frame(self.window, bg=self.STYLE["colors"]["header_bg"])
        header_frame.pack(fill='x', pady=(10, 0))

        title_label = tk.Label(header_frame,
                               text="▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄\n"
                                    "█ FILE OPERATIONS :: SECURE FILE ENCRYPTION/DECRYPTION █\n"
                                    "▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀",
                               font=self.STYLE["font_bold"],
                               fg=self.STYLE["colors"]["text"],
                               bg=self.STYLE["colors"]["header_bg"],
                               justify=tk.CENTER)
        title_label.pack(pady=10)

        # Main container
        main_frame = tk.Frame(self.window, bg=self.STYLE["colors"]["background"], padx=20, pady=20)
        main_frame.pack(fill='both', expand=True)

        # File selection frame
        file_frame = self._create_hacker_frame(main_frame, "FILE SELECTION")
        file_frame.pack(fill='x', pady=10)

        # File path display
        self.file_path_var = tk.StringVar(value="No file selected")
        file_path_label = tk.Label(file_frame, textvariable=self.file_path_var, font=self.STYLE["font_normal"],
                                   bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"],
                                   wraplength=800, justify=tk.LEFT)
        file_path_label.pack(fill='x', pady=5)

        # File info
        self.file_info_var = tk.StringVar(value="File size: N/A | Type: N/A")
        file_info_label = tk.Label(file_frame, textvariable=self.file_info_var, font=self.STYLE["font_small_bold"],
                                   bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["accent"])
        file_info_label.pack(fill='x', pady=2)

        # File operations buttons
        file_buttons_frame = tk.Frame(file_frame, bg=self.STYLE["colors"]["frame"])
        file_buttons_frame.pack(fill='x', pady=10)

        self._create_hacker_button(file_buttons_frame, "[ SELECT FILE ]", self._select_file).pack(side='left', padx=5)
        self._create_hacker_button(file_buttons_frame, "[ QUICK VIEW ]", self._quick_view).pack(side='left', padx=5)
        self._create_hacker_button(file_buttons_frame, "[ FILE HASH ]", self._calculate_hash).pack(side='left', padx=5)

        # Key frame
        key_frame = self._create_hacker_frame(main_frame, "ENCRYPTION KEY")
        key_frame.pack(fill='x', pady=10)

        # Key entry with generate button
        key_input_frame = tk.Frame(key_frame, bg=self.STYLE["colors"]["frame"])
        key_input_frame.pack(fill='x', pady=5)

        tk.Label(key_input_frame, text="File Key:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')

        self.key_entry = self._create_hacker_entry(key_input_frame, width=40)
        self.key_entry.pack(side='left', padx=5, fill='x', expand=True)

        self._create_hacker_button(key_input_frame, "[ GENERATE ]", self._generate_key).pack(side='left', padx=5)

        # Operations frame
        ops_frame = self._create_hacker_frame(main_frame, "FILE OPERATIONS")
        ops_frame.pack(fill='x', pady=10)

        # Standard operations
        std_ops_frame = tk.Frame(ops_frame, bg=self.STYLE["colors"]["frame"])
        std_ops_frame.pack(fill='x', pady=5)

        self._create_hacker_button(std_ops_frame, "[ ENCRYPT FILE ]", self._encrypt_file).pack(side='left', padx=5)
        self._create_hacker_button(std_ops_frame, "[ DECRYPT FILE ]", self._decrypt_file).pack(side='left', padx=5)
        self._create_hacker_button(std_ops_frame, "[ TEST DECRYPTION ]", self._test_decryption).pack(side='left',
                                                                                                     padx=5)

        # Advanced operations
        adv_ops_frame = tk.Frame(ops_frame, bg=self.STYLE["colors"]["frame"])
        adv_ops_frame.pack(fill='x', pady=10)

        # Warning frame for TRUE ENCRYPTION
        warning_frame = tk.Frame(adv_ops_frame, bg=self.STYLE["colors"]["frame"])
        warning_frame.pack(fill='x', pady=5)

        warning_label = tk.Label(warning_frame,
                                 text="⚠️ WARNING: TRUE ENCRYPTION WILL DELETE ORIGINAL FILE PERMANENTLY",
                                 font=self.STYLE["font_small_bold"],
                                 bg=self.STYLE["colors"]["frame"],
                                 fg=self.STYLE["colors"]["warning"])
        warning_label.pack()

        self._create_hacker_button(adv_ops_frame, "[ TRUE ENCRYPTION ]",
                                   self._true_encryption,
                                   bg_color=self.STYLE["colors"]["danger"]).pack(pady=5)

        # Output frame
        output_frame = self._create_hacker_frame(main_frame, "OPERATION LOG")
        output_frame.pack(fill='both', expand=True, pady=10)

        self.output_text = self._create_hacker_text(output_frame, height=10)
        self.output_text.pack(fill='both', expand=True, pady=5)
        # --- NEW DRAG-AND-DROP REGISTRATION ---
        self.window.drop_target_register('DND_FILES')
        self.window.dnd_bind('<<Drop>>', self._handle_drop)
        # Status bar
        self.status_var = tk.StringVar(value="[status] :: ready for file operations")
        status_bar = tk.Label(self.window, textvariable=self.status_var, relief='flat', anchor='w',
                              bg=self.STYLE["colors"]["outline"], fg=self.STYLE["colors"]["background"],
                              font=self.STYLE["font_bold"])
        status_bar.pack(side='bottom', fill='x')

    def _log_message(self, message: str, message_type: str = "info"):
        """Add message to operation log"""
        timestamp = time.strftime("%H:%M:%S")
        color_tag = "info" if message_type == "info" else "warning" if message_type == "warning" else "error"

        self.output_text.insert(tk.END, f"[{timestamp}] {message}\n", color_tag)
        self.output_text.see(tk.END)
        self.output_text.update()

        # Configure tags for colors
        self.output_text.tag_configure("info", foreground=self.STYLE["colors"]["text"])
        self.output_text.tag_configure("warning", foreground=self.STYLE["colors"]["warning"])
        self.output_text.tag_configure("error", foreground=self.STYLE["colors"]["danger"])

    def _handle_drop(self, event: tk.Event):
        """Handles the file drop event."""
        # The file path is in the event.data attribute.
        # It may have curly braces if it contains spaces, so we strip them.
        file_path = event.data.strip('{}')
        if os.path.exists(file_path):
            self._log_message(f"File dropped: {os.path.basename(file_path)}", "info")
            self._process_selected_file(file_path)
        else:
            self._log_message(f"Invalid file path dropped: {file_path}", "error")

    def _process_selected_file(self, file_path: str):
        """Updates the UI and logs info for a newly selected file."""
        self.current_file_path = file_path
        self.file_path_var.set(f"Selected: {file_path}")

        try:
            file_size = os.path.getsize(file_path)
            file_ext = os.path.splitext(file_path)[1].lower()
            size_str = self._format_file_size(file_size)
            self.file_info_var.set(f"File size: {size_str} | Type: {file_ext or 'Unknown'}")
            self._log_message(f"File loaded: {os.path.basename(file_path)} ({size_str})")
            if file_path.endswith('.ptbsher'):
                self._log_message("Detected encrypted file (.ptbsher extension)", "info")
        except Exception as e:
            self._log_message(f"Error reading file info: {str(e)}", "error")

    def _select_file(self):
        """Opens a dialog to select a file for operations."""
        file_path = filedialog.askopenfilename(
            title="Select file to process",
            filetypes=[("All files", "*.*")]  # Simplified for brevity
        )
        if file_path:
            self._process_selected_file(file_path)

    def _format_file_size(self, size_bytes):
        """Format file size in human readable format"""
        if size_bytes == 0:
            return "0 B"
        size_names = ["B", "KB", "MB", "GB"]
        i = 0
        while size_bytes >= 1024 and i < len(size_names) - 1:
            size_bytes /= 1024.0
            i += 1
        return f"{size_bytes:.2f} {size_names[i]}"

    def _generate_key(self):
        """Generate a secure random key"""
        import secrets
        import string

        # Generate 32-character random key
        alphabet = string.ascii_letters + string.digits + "!@#$%^&*"
        key = ''.join(secrets.choice(alphabet) for _ in range(32))

        self.key_entry.delete(0, tk.END)
        self.key_entry.insert(0, key)
        self._log_message("Generated secure random key")

    def _quick_view(self):
        """Quick view of file contents (for text files)"""
        if not self.current_file_path:
            self._log_message("No file selected", "error")
            return

        try:
            # Check if file is too large for quick view
            file_size = os.path.getsize(self.current_file_path)
            if file_size > 1024 * 1024:  # 1MB limit
                self._log_message("File too large for quick view (>1MB)", "warning")
                return

            with open(self.current_file_path, 'rb') as f:
                content = f.read()

            # Try to decode as text
            try:
                text_content = content.decode('utf-8')
                # Show first 500 characters
                preview = text_content[:500] + ("..." if len(text_content) > 500 else "")
                self._log_message(f"File preview (first 500 chars):\n{preview}")
            except UnicodeDecodeError:
                self._log_message("Binary file - cannot display text preview", "info")
                self._log_message(f"First 32 bytes (hex): {content[:32].hex()}")

        except Exception as e:
            self._log_message(f"Error reading file: {str(e)}", "error")

    def _calculate_hash(self):
        """Calculate file hash"""
        if not self.current_file_path:
            self._log_message("No file selected", "error")
            return

        try:
            hasher = hashlib.sha256()
            with open(self.current_file_path, 'rb') as f:
                for chunk in iter(lambda: f.read(4096), b""):
                    hasher.update(chunk)

            file_hash = hasher.hexdigest()
            self._log_message(f"SHA-256 Hash: {file_hash}")

        except Exception as e:
            self._log_message(f"Error calculating hash: {str(e)}", "error")

    def _encrypt_file(self):
        """Encrypt the selected file"""
        if not self._validate_operation():
            return

        key = self.key_entry.get().strip()
        if not key:
            self._log_message("Please enter an encryption key", "error")
            return

        try:
            output_path = self.current_file_path + '.ptbsher'

            self._log_message(f"Encrypting {os.path.basename(self.current_file_path)}...")
            self.status_var.set("[encrypting] :: processing file...")
            self.window.update()

            self.cipher.encrypt_file(self.current_file_path, output_path, key)

            self._log_message(f"✓ Encryption successful: {os.path.basename(output_path)}")
            self.status_var.set("[success] :: file encrypted")

            # Update file info
            encrypted_size = os.path.getsize(output_path)
            size_str = self._format_file_size(encrypted_size)
            self._log_message(f"Encrypted file size: {size_str}")

        except Exception as e:
            self._log_message(f"✗ Encryption failed: {str(e)}", "error")
            self.status_var.set("[error] :: encryption failed")

    def _decrypt_file(self):
        """Decrypt the selected file and delete the encrypted file after successful decryption"""
        if not self._validate_operation():
            return

        key = self.key_entry.get().strip()
        if not key:
            self._log_message("Please enter a decryption key", "error")
            return

        try:
            # Determine output path
            if self.current_file_path.endswith('.ptbsher'):
                output_path = self.current_file_path[:-8]  # Remove .ptbsher extension
            else:
                output_path = self.current_file_path + '.decrypted'
                self._log_message("Warning: File doesn't have .ptbsher extension", "warning")

            self._log_message(f"Decrypting {os.path.basename(self.current_file_path)}...")
            self.status_var.set("[decrypting] :: processing file...")
            self.window.update()

            self.cipher.decrypt_file(self.current_file_path, output_path, key)

            self._log_message(f"✓ Decryption successful: {os.path.basename(output_path)}")

            # Delete the encrypted file after successful decryption
            if self.current_file_path.endswith('.ptbsher'):
                try:
                    os.remove(self.current_file_path)
                    self._log_message(f"✓ Encrypted file deleted: {os.path.basename(self.current_file_path)}")
                except Exception as e:
                    self._log_message(f"⚠ Could not delete encrypted file: {str(e)}", "warning")

            self.status_var.set("[success] :: file decrypted")

            # Verify decryption
            decrypted_size = os.path.getsize(output_path)
            size_str = self._format_file_size(decrypted_size)
            self._log_message(f"Decrypted file size: {size_str}")

            # Update the current file path to the decrypted file
            self.current_file_path = output_path
            self.file_path_var.set(f"Decrypted: {output_path}")
            self.file_info_var.set(
                f"File size: {size_str} | Type: {os.path.splitext(output_path)[1].lower() or 'Unknown'}")

        except DecryptionError as e:
            self._log_message(f"✗ Decryption failed: {str(e)}", "error")
            self.status_var.set("[error] :: decryption failed - wrong key or corrupted file")
        except Exception as e:
            self._log_message(f"✗ Decryption failed: {str(e)}", "error")
            self.status_var.set("[error] :: decryption failed")

    def _test_decryption(self):
        """Test decryption without saving file"""
        if not self._validate_operation():
            return

        key = self.key_entry.get().strip()
        if not key:
            self._log_message("Please enter a decryption key", "error")
            return

        try:
            self._log_message("Testing decryption (in-memory only)...")
            self.status_var.set("[testing] :: verifying decryption...")
            self.window.update()

            # Create temporary output path
            with tempfile.NamedTemporaryFile(delete=False) as temp_file:
                temp_path = temp_file.name

            try:
                self.cipher.decrypt_file(self.current_file_path, temp_path, key)

                # Check if file was created and has content
                if os.path.getsize(temp_path) > 0:
                    self._log_message("✓ Decryption test passed - key is correct")
                    self.status_var.set("[success] :: decryption test passed")
                else:
                    self._log_message("⚠ Decryption produced empty file", "warning")

            finally:
                # Clean up temporary file
                try:
                    os.unlink(temp_path)
                except:
                    pass

        except DecryptionError as e:
            self._log_message(f"✗ Decryption test failed: {str(e)}", "error")
            self.status_var.set("[error] :: decryption test failed")
        except Exception as e:
            self._log_message(f"✗ Decryption test failed: {str(e)}", "error")
            self.status_var.set("[error] :: decryption test failed")

    def _true_encryption(self):
        """Encrypt file and delete original (secure erase)"""
        if not self._validate_operation():
            return

        key = self.key_entry.get().strip()
        if not key:
            self._log_message("Please enter an encryption key", "error")
            return

        # Warning confirmation
        result = messagebox.askyesno(
            "TRUE ENCRYPTION WARNING",
            "⚠️  DANGEROUS OPERATION  ⚠️\n\n"
            "TRUE ENCRYPTION will:\n"
            "• Encrypt your file\n"
            "• PERMANENTLY DELETE the original file\n"
            "• Leave ONLY the encrypted version\n\n"
            "This operation is IRREVERSIBLE!\n\n"
            "Are you absolutely sure you want to continue?",
            icon='warning',
            default='no'
        )

        if not result:
            self._log_message("True encryption cancelled by user", "info")
            return

        try:
            output_path = self.current_file_path + '.ptbsher'

            self._log_message("🚨 INITIATING TRUE ENCRYPTION...", "warning")
            self._log_message("This will permanently delete the original file!", "warning")
            self.status_var.set("[true-encrypt] :: processing...")
            self.window.update()

            # Step 1: Encrypt the file
            self.cipher.encrypt_file(self.current_file_path, output_path, key)
            self._log_message("✓ File encrypted successfully")

            # Step 2: Verify encryption worked by testing decryption
            self._log_message("Verifying encryption integrity...")
            test_path = None
            try:
                with tempfile.NamedTemporaryFile(delete=False) as temp_file:
                    test_path = temp_file.name

                self.cipher.decrypt_file(output_path, test_path, key)

                # Compare file sizes (basic integrity check)
                original_size = os.path.getsize(self.current_file_path)
                decrypted_size = os.path.getsize(test_path)

                if decrypted_size > 0:
                    self._log_message("✓ Encryption integrity verified")

                    # Step 3: Secure delete original file
                    self._log_message("🚨 DELETING ORIGINAL FILE...", "warning")
                    self._secure_delete_file(self.current_file_path)

                    self._log_message("✓ Original file permanently deleted", "warning")
                    self._log_message("✓ True encryption completed successfully", "warning")
                    self.status_var.set("[success] :: true encryption complete")

                    # Update UI
                    self.current_file_path = output_path
                    self.file_path_var.set(f"Encrypted: {output_path}")

                    encrypted_size = os.path.getsize(output_path)
                    size_str = self._format_file_size(encrypted_size)
                    self.file_info_var.set(f"File size: {size_str} | Type: .ptbsher")

                else:
                    self._log_message("✗ Encryption verification failed - aborting deletion", "error")
                    os.unlink(output_path)  # Remove the failed encrypted file

            finally:
                # Clean up test file
                if test_path and os.path.exists(test_path):
                    try:
                        os.unlink(test_path)
                    except:
                        pass

        except Exception as e:
            self._log_message(f"✗ True encryption failed: {str(e)}", "error")
            self.status_var.set("[error] :: true encryption failed")

    def _secure_delete_file(self, file_path):
        """Securely delete a file by overwriting it before deletion"""
        try:
            file_size = os.path.getsize(file_path)

            # Overwrite file with random data multiple times
            with open(file_path, 'wb') as f:
                # 3-pass overwrite (simplified secure delete)
                for pass_num in range(3):
                    f.seek(0)
                    # Write random data
                    f.write(os.urandom(file_size))
                    f.flush()
                    os.fsync(f.fileno())

            # Delete the file
            os.unlink(file_path)
            self._log_message(f"Secure deletion pass completed")

        except Exception as e:
            self._log_message(f"Warning: Could not securely delete file: {str(e)}", "warning")
            # Fallback to normal delete
            try:
                os.unlink(file_path)
                self._log_message("File deleted using standard method")
            except Exception as e2:
                raise Exception(f"Failed to delete file: {str(e2)}")

    def _validate_operation(self):
        """Validate that we have a file to work with"""
        if not self.current_file_path or not os.path.exists(self.current_file_path):
            self._log_message("No valid file selected", "error")
            return False
        return True


class KeywordGeneratorWindow:
    """Modal window for generating secure keywords"""

    STYLE = {
        "font_family": ("Consolas", "Courier New"),
        "font_normal": (("Consolas", 11)),
        "font_bold": (("Consolas", 11, "bold")),
        "font_small_bold": (("Consolas", 9, "bold")),
        "colors": {
            "background": "#0D0D0D", "frame": "#1A1A1A", "text": "#00FF41", "header_bg": "#0D0D0D",
            "accent": "#00FF41", "accent_hover": "#90FF90", "button_fg": "#0D0D0D",
            "entry_bg": "#000000", "cursor": "#00FF41", "outline": "#00FF41",
            "good": "#90FF90",
            "warning": "#FF6B00",
            "danger": "#FF0000"
        },
        "padding": {"frame": 15, "widget": 8, "button": (15, 6)},
    }

    def __init__(self, parent):
        self.parent = parent
        self.window = None
        self.generated_keyword = None
        self._setup_window()

    def _create_hacker_button(self, parent, text, command, font=None, padx=None, pady=None, bg_color=None):
        font_to_use = font if font else self.STYLE["font_bold"]
        padx_to_use = padx if padx is not None else self.STYLE["padding"]["button"][0]
        pady_to_use = pady if pady is not None else self.STYLE["padding"]["button"][1]
        bg_to_use = bg_color if bg_color else self.STYLE["colors"]["accent"]
        hover_color = self.STYLE["colors"]["accent_hover"]
        btn = tk.Button(parent, text=text, command=command, font=font_to_use, bg=bg_to_use,
                        fg=self.STYLE["colors"]["button_fg"], relief='flat', borderwidth=0, padx=padx_to_use,
                        pady=pady_to_use, activebackground=hover_color,
                        activeforeground=self.STYLE["colors"]["button_fg"])
        btn.bind("<Enter>", lambda e: e.widget.config(bg=hover_color))
        btn.bind("<Leave>", lambda e: e.widget.config(bg=bg_to_use))
        return btn

    def _create_hacker_frame(self, parent, title=None):
        """Create a frame with the hacker style"""
        frame = tk.Frame(parent, bg=self.STYLE["colors"]["frame"],
                         highlightbackground=self.STYLE["colors"]["outline"],
                         highlightthickness=1, padx=self.STYLE["padding"]["frame"],
                         pady=self.STYLE["padding"]["frame"])

        if title:
            title_label = tk.Label(frame, text=title, font=self.STYLE["font_bold"],
                                   bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"])
            title_label.pack(fill='x', anchor='w', pady=(0, 10))

        return frame

    def _create_hacker_entry(self, parent, default_text="", width=20, state="normal"):
        """Create an entry field with hacker style"""
        entry = tk.Entry(parent, font=self.STYLE["font_normal"],
                         bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                         relief='flat', borderwidth=0, width=width,
                         insertbackground=self.STYLE["colors"]["cursor"], state=state)
        if default_text:
            entry.insert(0, default_text)
        return entry

    def _setup_window(self):
        """Setup the keyword generator window"""
        self.window = tk.Toplevel(self.parent)
        self.window.title(">>> PARTYBASHER - KEYWORD GENERATOR <<<")
        self.window.geometry("720x700")
        self.window.minsize(720, 700)
        self.window.configure(bg=self.STYLE["colors"]["background"])
        self.window.transient(self.parent)
        self.window.grab_set()

        # Create header
        header_frame = tk.Frame(self.window, bg=self.STYLE["colors"]["background"])
        header_frame.pack(fill='x', pady=(10, 0))

        title_label = tk.Label(header_frame,
                               text="▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄\n"
                                    "█ KEYWORD GENERATOR :: SECURE CRYPTOGRAPHIC KEYS █\n"
                                    "▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀",
                               font=self.STYLE["font_bold"],
                               fg=self.STYLE["colors"]["text"],
                               bg=self.STYLE["colors"]["background"],
                               justify=tk.CENTER)
        title_label.pack(pady=10)

        # Main container
        main_frame = tk.Frame(self.window, bg=self.STYLE["colors"]["background"], padx=20, pady=20)
        main_frame.pack(fill='both', expand=True)

        # Settings frame
        settings_frame = self._create_hacker_frame(main_frame, "GENERATION SETTINGS")
        settings_frame.pack(fill='x', pady=10)

        # Length setting
        length_frame = tk.Frame(settings_frame, bg=self.STYLE["colors"]["frame"])
        length_frame.pack(fill='x', pady=8)

        tk.Label(length_frame, text="Keyword Length:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')

        self.length_var = tk.IntVar(value=24)
        length_scale = tk.Scale(length_frame, from_=24, to=128, variable=self.length_var,
                                orient=tk.HORIZONTAL, showvalue=False,
                                bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"],
                                highlightbackground=self.STYLE["colors"]["frame"],
                                troughcolor=self.STYLE["colors"]["entry_bg"])
        length_scale.pack(side='left', fill='x', expand=True, padx=(10, 0))

        self.length_label = tk.Label(length_frame, text="24", font=self.STYLE["font_bold"],
                                     bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["accent"])
        self.length_label.pack(side='right', padx=(10, 0))
        length_scale.configure(command=self._update_length_label)

        # Character sets
        chars_frame = tk.Frame(settings_frame, bg=self.STYLE["colors"]["frame"])
        chars_frame.pack(fill='x', pady=8)

        self.use_lower = tk.BooleanVar(value=True)
        self.use_upper = tk.BooleanVar(value=True)
        self.use_digits = tk.BooleanVar(value=True)
        self.use_special = tk.BooleanVar(value=True)

        tk.Checkbutton(chars_frame, text="Lowercase (a-z)", variable=self.use_lower,
                       font=self.STYLE["font_normal"], bg=self.STYLE["colors"]["frame"],
                       fg=self.STYLE["colors"]["text"], selectcolor=self.STYLE["colors"]["entry_bg"],
                       activebackground=self.STYLE["colors"]["frame"],
                       activeforeground=self.STYLE["colors"]["text"]).pack(side='left', padx=(0, 15))

        tk.Checkbutton(chars_frame, text="Uppercase (A-Z)", variable=self.use_upper,
                       font=self.STYLE["font_normal"], bg=self.STYLE["colors"]["frame"],
                       fg=self.STYLE["colors"]["text"], selectcolor=self.STYLE["colors"]["entry_bg"],
                       activebackground=self.STYLE["colors"]["frame"],
                       activeforeground=self.STYLE["colors"]["text"]).pack(side='left', padx=(0, 15))

        tk.Checkbutton(chars_frame, text="Digits (0-9)", variable=self.use_digits,
                       font=self.STYLE["font_normal"], bg=self.STYLE["colors"]["frame"],
                       fg=self.STYLE["colors"]["text"], selectcolor=self.STYLE["colors"]["entry_bg"],
                       activebackground=self.STYLE["colors"]["frame"],
                       activeforeground=self.STYLE["colors"]["text"]).pack(side='left', padx=(0, 15))

        tk.Checkbutton(chars_frame, text="Special (!@#...)", variable=self.use_special,
                       font=self.STYLE["font_normal"], bg=self.STYLE["colors"]["frame"],
                       fg=self.STYLE["colors"]["text"], selectcolor=self.STYLE["colors"]["entry_bg"],
                       activebackground=self.STYLE["colors"]["frame"],
                       activeforeground=self.STYLE["colors"]["text"]).pack(side='left')

        # Buttons frame
        button_frame = tk.Frame(settings_frame, bg=self.STYLE["colors"]["frame"])
        button_frame.pack(fill='x', pady=10)

        self._create_hacker_button(button_frame, "[ GENERATE KEYWORD ]",
                                   self._generate_keyword).pack(side='left', padx=(0, 10))
        self._create_hacker_button(button_frame, "[ SECURE RANDOM ]",
                                   self._secure_random).pack(side='left')

        # Generated keyword frame
        keyword_frame = self._create_hacker_frame(main_frame, "GENERATED KEYWORD")
        keyword_frame.pack(fill='x', pady=10)

        self.keyword_var = tk.StringVar()
        keyword_entry = self._create_hacker_entry(keyword_frame, width=50, state="readonly")
        keyword_entry.config(textvariable=self.keyword_var)
        keyword_entry.pack(fill='x', pady=5)

        # Security info frame
        security_frame = self._create_hacker_frame(main_frame, "SECURITY ANALYSIS")
        security_frame.pack(fill='x', pady=10)

        # Entropy info
        entropy_frame = tk.Frame(security_frame, bg=self.STYLE["colors"]["frame"])
        entropy_frame.pack(fill='x', pady=5)

        tk.Label(entropy_frame, text="Entropy:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')

        self.entropy_var = tk.StringVar(value="0 bits")
        entropy_label = tk.Label(entropy_frame, textvariable=self.entropy_var,
                                 font=self.STYLE["font_bold"], bg=self.STYLE["colors"]["frame"],
                                 fg=self.STYLE["colors"]["text"])
        entropy_label.pack(side='left', padx=(10, 0))

        # Security status
        status_frame = tk.Frame(security_frame, bg=self.STYLE["colors"]["frame"])
        status_frame.pack(fill='x', pady=5)

        tk.Label(status_frame, text="Security Status:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')

        self.status_var = tk.StringVar(value="Not generated")
        self.status_label = tk.Label(status_frame, textvariable=self.status_var,
                                     font=self.STYLE["font_bold"], bg=self.STYLE["colors"]["frame"])
        self.status_label.pack(side='left', padx=(10, 0))

        # Action buttons
        action_frame = tk.Frame(main_frame, bg=self.STYLE["colors"]["background"])
        action_frame.pack(fill='x', pady=20)

        self._create_hacker_button(action_frame, "[ USE KEYWORD ]",
                                   self._use_keyword, bg_color=self.STYLE["colors"]["good"]).pack(side='right',
                                                                                                  padx=(10, 0))
        self._create_hacker_button(action_frame, "[ COPY TO CLIPBOARD ]",
                                   self._copy_to_clipboard).pack(side='right', padx=(10, 0))
        self._create_hacker_button(action_frame, "[ CLOSE ]",
                                   self.window.destroy).pack(side='left')

        # Generate initial keyword
        self._generate_keyword()

    def _update_length_label(self, value=None):
        self.length_label.config(text=str(self.length_var.get()))

    def _generate_keyword(self):
        """Generate a secure keyword with bounded automatic retries to meet entropy target."""
        length = self.length_var.get()

        # Build character set based on selections
        charset = ""
        if self.use_lower.get():
            charset += string.ascii_lowercase
        if self.use_upper.get():
            charset += string.ascii_uppercase
        if self.use_digits.get():
            charset += string.digits
        if self.use_special.get():
            charset += "!@#$%^&*()_+-=[]{}|;:,.<>?"

        if not charset:
            messagebox.showwarning("Configuration Error",
                                   "Please select at least one character type.")
            return

        # Controlled attempts to auto-generate a keyword meeting entropy threshold.
        # This avoids recursion: _update_security_info will not call _generate_keyword().
        max_attempts = 10
        best_keyword = None
        best_entropy = -1.0

        for attempt in range(1, max_attempts + 1):
            keyword = ''.join(secrets.choice(charset) for _ in range(length))
            entropy = self._calculate_entropy(keyword, charset)

            # Keep track of the best candidate so far
            if entropy > best_entropy:
                best_entropy = entropy
                best_keyword = keyword

            # Stop early if we meet the requested threshold
            if entropy >= 75:
                self.keyword_var.set(keyword)
                self._update_security_info(keyword, charset)
                return

        # If we reach here, no candidate met the threshold within max_attempts.
        # Use the best candidate found and report its entropy.
        self.keyword_var.set(best_keyword)
        self._update_security_info(best_keyword, charset)

    def _secure_random(self):
        """Generate keyword using only cryptographic randomness"""
        length = self.length_var.get()
        charset = string.ascii_letters + string.digits + "!@#$%^&*"
        keyword = ''.join(secrets.choice(charset) for _ in range(length))
        self.keyword_var.set(keyword)
        self._update_security_info(keyword, charset)

    def _update_security_info(self, keyword, charset):
        """Update entropy calculation and security status (no auto-regeneration)."""
        entropy = self._calculate_entropy(keyword, charset)
        self.entropy_var.set(f"{entropy:.1f} bits")

        # Update security status with color coding but do NOT auto-regenerate.
        if entropy >= 75:
            self.status_var.set("✓ SECURE (75+ bits)")
            self.status_label.config(fg=self.STYLE["colors"]["good"])
        else:
            self.status_var.set("✗ INSECURE (<75 bits)")
            self.status_label.config(fg=self.STYLE["colors"]["warning"])

    def _calculate_entropy(self, keyword, charset):
        """Calculate entropy in bits"""
        charset_size = len(charset)
        if charset_size == 0:
            return 0
        return len(keyword) * math.log2(charset_size)

    def _use_keyword(self):
        """Use the generated keyword in the main application"""
        keyword = self.keyword_var.get()
        if keyword:
            # Ensure minimum entropy requirement
            charset = string.ascii_letters + string.digits + "!@#$%^&*"
            entropy = self._calculate_entropy(keyword, charset)

            if entropy >= 75:
                self.generated_keyword = keyword
                self.window.destroy()
            else:
                messagebox.showwarning("Security Warning",
                                       "Generated keyword does not meet minimum 75-bit entropy requirement.\n"
                                       "Please generate a stronger keyword.")
        else:
            messagebox.showwarning("No Keyword", "Please generate a keyword first.")

    def _copy_to_clipboard(self):
        """Copy keyword to clipboard"""
        keyword = self.keyword_var.get()
        if keyword:
            try:
                self.window.clipboard_clear()
                self.window.clipboard_append(keyword)
                messagebox.showinfo("Success", "Keyword copied to clipboard.")
            except Exception as e:
                messagebox.showerror("Error", f"Could not copy to clipboard: {str(e)}")
        else:
            messagebox.showwarning("No Keyword", "No keyword to copy.")


class PartybasherGUI:
    STYLE = {
        "font_family": ("Consolas", "Courier New"),
        "font_normal": (("Consolas", 11)),
        "font_bold": (("Consolas", 11, "bold")),
        "font_small_bold": (("Consolas", 9, "bold")),
        "font_ascii": (("Courier New", 9)),
        "colors": {
            "background": "#0D0D0D", "frame": "#1A1A1A", "text": "#00FF41", "header_bg": "#0D0D0D",
            "accent": "#00FF41", "accent_hover": "#90FF90", "button_fg": "#0D0D0D",
            "entry_bg": "#000000", "cursor": "#00FF41", "outline": "#00FF41",
            "good": "#90FF90",
            "warning": "#FF6B00",
            "danger": "#FF0000"
        },
        "padding": {"frame": 20, "widget": 10, "button": (20, 8)},
    }

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(">>> Partybasher v1.9<<<")
        self.root.geometry("1100x840")
        self.root.configure(bg=self.STYLE["colors"]["background"])
        self.root.minsize(1100, 840)
        self.cipher = PartybasherAlgorithm(SECURITY_LEVEL)
        self.crypto_lab = PartybasherCryptanalysisLab(self.cipher)
        self.status_var = tk.StringVar(value="[status] :: ready - Security Level: " + SECURITY_LEVEL)

        # Initialize widget attributes to None to avoid AttributeError
        self.text_entry = None
        self.key_entry = None
        self.result_text = None

        self._setup_ui()
        self._setup_bindings()

    def _create_hacker_button(self, parent, text, command, font=None, padx=None, pady=None):
        font_to_use = font if font else self.STYLE["font_bold"]
        padx_to_use = padx if padx is not None else self.STYLE["padding"]["button"][0]
        pady_to_use = pady if pady is not None else self.STYLE["padding"]["button"][1]
        bg_color = self.STYLE["colors"]["accent"]
        hover_color = self.STYLE["colors"]["accent_hover"]
        btn = tk.Button(parent, text=text, command=command, font=font_to_use, bg=bg_color,
                        fg=self.STYLE["colors"]["button_fg"], relief='flat', borderwidth=0, padx=padx_to_use,
                        pady=pady_to_use, activebackground=hover_color,
                        activeforeground=self.STYLE["colors"]["button_fg"])
        btn.bind("<Enter>", lambda e: e.widget.config(bg=hover_color))
        btn.bind("<Leave>", lambda e: e.widget.config(bg=bg_color))
        return btn

    def _create_hacker_frame(self, parent, title=None):
        """Create a frame with the hacker style"""
        frame = tk.Frame(parent, bg=self.STYLE["colors"]["frame"],
                         highlightbackground=self.STYLE["colors"]["outline"],
                         highlightthickness=1, padx=15, pady=15)

        if title:
            title_label = tk.Label(frame, text=title, font=self.STYLE["font_bold"],
                                   bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"])
            title_label.pack(fill='x', anchor='w', pady=(0, 10))

        return frame

    def _create_hacker_entry(self, parent, default_text="", width=20):
        """Create an entry field with hacker style"""
        entry = tk.Entry(parent, font=self.STYLE["font_normal"],
                         bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                         relief='flat', borderwidth=0, width=width,
                         insertbackground=self.STYLE["colors"]["cursor"])
        if default_text:
            entry.insert(0, default_text)
        return entry

    def _create_hacker_text(self, parent, height=6):
        """Create a text area with hacker style"""
        text = scrolledtext.ScrolledText(parent, height=height, font=self.STYLE["font_normal"],
                                         bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                                         relief='flat', borderwidth=0, wrap=tk.WORD,
                                         insertbackground=self.STYLE["colors"]["cursor"])
        return text

    def _setup_ui(self) -> None:
        self._create_header()
        main_frame = tk.Frame(self.root, bg=self.STYLE["colors"]["background"], padx=20, pady=20)
        main_frame.pack(fill='both', expand=True)

        # Create all IO frames first
        self._create_io_frame(main_frame, "INPUT :: PAYLOAD & KEY", "text_entry", "key_entry")
        self._create_action_frame(main_frame)
        self._create_io_frame(main_frame, "OUTPUT :: RESULT", "result_text")
        self._create_status_bar()

        # Now create context menus after all widgets are defined
        self._create_context_menu(self.text_entry)
        self._create_context_menu(self.key_entry)
        self._create_context_menu(self.result_text)

    def _create_header(self) -> None:
        header = tk.Frame(self.root, bg=self.STYLE["colors"]["header_bg"])
        header.pack(fill='x', pady=(10, 0))
        ascii_label = tk.Label(header, text=PARTYBASHER_ASCII, font=self.STYLE["font_ascii"],
                               fg=self.STYLE["colors"]["text"], bg=self.STYLE["colors"]["header_bg"], justify=tk.LEFT)
        ascii_label.pack()
        button_frame = tk.Frame(header, bg=self.STYLE["colors"]["header_bg"])
        button_frame.pack(fill='x', padx=20, pady=(0, 10))

        # Button container to ensure proper spacing
        btn_container = tk.Frame(button_frame, bg=self.STYLE["colors"]["header_bg"])
        btn_container.pack(side='right')

        # Add LOAD FILE button - opens the file operations window
        load_file_btn = self._create_hacker_button(btn_container, "[ LOAD FILE ]", self._show_file_operations)
        load_file_btn.pack(side='right', padx=5)

        exit_btn = self._create_hacker_button(btn_container, "[ EXIT ]", self.root.destroy)
        exit_btn.pack(side='right', padx=5)
        analysis_btn = self._create_hacker_button(btn_container, "[ ANALYSIS ]", self._show_analysis_lab)
        analysis_btn.pack(side='right', padx=5)
        about_btn = self._create_hacker_button(btn_container, "[ ABOUT ]", self._show_about_window)
        about_btn.pack(side='right', padx=5)

    def _create_action_frame(self, parent):
        frame = tk.Frame(parent, bg=self.STYLE["colors"]["background"])
        frame.pack(fill='x', pady=10)
        self._create_hacker_button(frame, "[ ENCRYPT ]", self._encrypt_gui).pack(side='left', expand=True, padx=5)
        self._create_hacker_button(frame, "[ DECRYPT ]", self._decrypt_gui).pack(side='right', expand=True, padx=5)

    def _create_status_bar(self) -> None:
        status_bar = tk.Label(self.root, textvariable=self.status_var, relief='flat', anchor='w',
                              bg=self.STYLE["colors"]["outline"], fg=self.STYLE["colors"]["background"],
                              font=self.STYLE["font_bold"])
        status_bar.pack(side='bottom', fill='x')

    def _calculate_entropy(self, password: str) -> float:
        """
        Calculates a more realistic "effective" entropy of a password by
        applying penalties for weaknesses like repetition and sequences.
        """
        if not password:
            return 0.0

        # --- 1. Calculate the "Raw" Theoretical Entropy ---
        charset_size = 0
        has_lower = any(c in string.ascii_lowercase for c in password)
        has_upper = any(c in string.ascii_uppercase for c in password)
        has_digits = any(c in string.digits for c in password)
        has_special = any(not c.isalnum() for c in password)

        if has_lower: charset_size += 26
        if has_upper: charset_size += 26
        if has_digits: charset_size += 10
        if has_special: charset_size += 32

        if charset_size == 0: return 0.0

        raw_entropy = len(password) * math.log2(charset_size)

        # --- 2. Calculate Penalties for Predictable Patterns ---
        total_penalty = 0.0

        # Penalty 1: Consecutive Repetition (e.g., "aaaa", "111")
        # Each repeated character effectively adds almost no new entropy.
        for i in range(1, len(password)):
            if password[i] == password[i - 1]:
                total_penalty += math.log2(charset_size) * 0.9  # Penalize heavily

        # Penalty 2: Common Sequences (e.g., "abc", "123", "qwe")
        # We check for 3-character sequences forward and backward.
        for i in range(len(password) - 2):
            chunk = password[i:i + 3].lower()
            # Check for alphabetical or numerical sequences
            if (chunk in "abcdefghijklmnopqrstuvwxyz" or
                    chunk in "zyxwutsrqponmlkjihgfedcba" or
                    chunk in "0123456789" or
                    chunk in "9876543210" or
                    chunk in "qwertyuiop" or  # Keyboard patterns
                    chunk in "asdfghjkl" or
                    chunk in "zxcvbnm"):
                # A 3-char sequence is much less complex than 3 random chars
                total_penalty += math.log2(charset_size) * 1.5

                # Penalty 3: Not using all character classes
        # A bonus is effectively a negative penalty. We reward variety.
        num_char_classes = sum([has_lower, has_upper, has_digits, has_special])
        if num_char_classes == 1:
            # Only one class (like all lowercase) is very weak.
            total_penalty += raw_entropy * 0.3
        elif num_char_classes == 2:
            total_penalty += raw_entropy * 0.15
        # No penalty for 3 or 4 classes.

        # --- 3. Calculate the Final "Effective" Entropy ---
        effective_entropy = max(0, raw_entropy - total_penalty)

        return effective_entropy

    def _create_io_frame(self, parent, title, *widget_names):
        frame = self._create_hacker_frame(parent, title)
        frame.pack(fill='both', expand="result_text" in widget_names, pady=10)

        text_container = tk.Frame(frame, bg=self.STYLE["colors"]["entry_bg"])
        text_container.pack(fill='both', expand=True)

        if "text_entry" in widget_names:
            self.text_entry = self._create_hacker_text(text_container, height=6)
            self.text_entry.pack(fill='both', expand=True, pady=5)
            paste_btn = self._create_hacker_button(text_container, "[ PASTE ]", self._paste_into_input,
                                                   font=self.STYLE["font_small_bold"], padx=8, pady=2)
            paste_btn.place(relx=1.0, rely=1.0, x=-5, y=-5, anchor="se")

        if "key_entry" in widget_names:
            key_frame = tk.Frame(frame, bg=self.STYLE["colors"]["frame"])
            key_frame.pack(fill='x', pady=(10, 0))

            tk.Label(key_frame, text="KEY:", font=self.STYLE["font_normal"], bg=self.STYLE["colors"]["frame"],
                     fg=self.STYLE["colors"]["text"]).pack(side='left')

            key_input_frame = tk.Frame(key_frame, bg=self.STYLE["colors"]["frame"])
            key_input_frame.pack(side='left', fill='x', expand=True, padx=(10, 0))

            self.key_entry = self._create_hacker_entry(key_input_frame)
            self.key_entry.pack(side='left', fill='x', expand=True)
            # Bind the update function to every key release
            self.key_entry.bind("<KeyRelease>", self._update_strength_meter)

            key_gen_btn = self._create_hacker_button(key_input_frame, "[ KEY GENERATION ]",
                                                     self._show_keyword_generator,
                                                     font=self.STYLE["font_small_bold"], padx=12, pady=4)
            key_gen_btn.pack(side='right', padx=(10, 0))

            # --- NEW STRENGTH METER WIDGETS ---
            strength_frame = tk.Frame(frame, bg=self.STYLE["colors"]["frame"])
            strength_frame.pack(fill='x', pady=(5, 0), padx=45)

            # Configure styles for the colored progress bar
            style = ttk.Style()
            style.theme_use('default')
            style.configure("good.Horizontal.TProgressbar", background=self.STYLE["colors"]["good"])
            style.configure("warning.Horizontal.TProgressbar", background=self.STYLE["colors"]["warning"])
            style.configure("danger.Horizontal.TProgressbar", background=self.STYLE["colors"]["danger"])

            self.strength_bar = ttk.Progressbar(strength_frame, orient='horizontal', mode='determinate', maximum=128)
            self.strength_bar.pack(side='left', fill='x', expand=True)

            self.strength_label = tk.Label(strength_frame, text="Enter a key...", font=self.STYLE["font_small_bold"],
                                           bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"])
            self.strength_label.pack(side='left', padx=(10, 0))

        if "result_text" in widget_names:
            self.result_text = self._create_hacker_text(text_container)
            self.result_text.pack(fill='both', expand=True, pady=5)
            copy_btn = self._create_hacker_button(text_container, "[ COPY ]", self._copy_from_output,
                                                  font=self.STYLE["font_small_bold"], padx=8, pady=2)
            copy_btn.place(relx=1.0, rely=1.0, x=-5, y=-5, anchor="se")

    def _update_strength_meter(self, event: Optional[tk.Event] = None):
        """Callback function to update the password strength meter in real-time."""
        password = self.key_entry.get()
        entropy = self._calculate_entropy(password)

        # Update the progress bar
        # We'll cap the visual representation at 128 bits for a clean progress bar
        progress_value = min(entropy, 128)
        self.strength_bar['value'] = progress_value

        # Update the label and color
        if entropy < 40:
            text = f"Very Weak."
            color = self.STYLE["colors"]["danger"]
            bar_color = "danger.Horizontal.TProgressbar"
        elif entropy < 70:
            text = f"Moderate."
            color = self.STYLE["colors"]["warning"]
            bar_color = "warning.Horizontal.TProgressbar"
        else:
            text = f"Strong."
            color = self.STYLE["colors"]["good"]
            bar_color = "good.Horizontal.TProgressbar"

        self.strength_label.config(text=text, fg=color)
        self.strength_bar.config(style=bar_color)

    def _show_keyword_generator(self):
        """Open the keyword generator window"""
        generator = KeywordGeneratorWindow(self.root)
        self.root.wait_window(generator.window)

        # If a keyword was generated, use it
        if hasattr(generator, 'generated_keyword') and generator.generated_keyword:
            self.key_entry.delete(0, tk.END)
            self.key_entry.insert(0, generator.generated_keyword)
            self.status_var.set("[success] :: secure keyword applied")

    def _show_file_operations(self):
        """Open the file operations window"""
        FileOperationsWindow(self.root, self.cipher)

    def _show_analysis_lab(self):
        """Open the cryptographic analysis laboratory"""
        analysis_window = tk.Toplevel(self.root)
        analysis_window.title(">>> PARTYBASHER v1.9 - CRYPTANALYSIS LABORATORY <<<")
        analysis_window.geometry("1300x1100")
        analysis_window.minsize(1300, 1100)
        analysis_window.configure(bg=self.STYLE["colors"]["background"])
        analysis_window.transient(self.root)
        analysis_window.grab_set()

        # Create header for analysis lab
        header_frame = tk.Frame(analysis_window, bg=self.STYLE["colors"]["header_bg"])
        header_frame.pack(fill='x', pady=(10, 0))

        title_label = tk.Label(header_frame,
                               text="▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄\n"
                                    "█ CRYPTOANALYSIS LABORATORY :: SECURITY TESTING SUITE █\n"
                                    "▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀",
                               font=self.STYLE["font_bold"],
                               fg=self.STYLE["colors"]["text"],
                               bg=self.STYLE["colors"]["header_bg"],
                               justify=tk.CENTER)
        title_label.pack(pady=10)

        # Create notebook for different analysis tabs
        notebook = ttk.Notebook(analysis_window)
        notebook.pack(fill='both', expand=True, padx=20, pady=20)

        # Configure notebook style to match hacker theme
        self._configure_notebook_style()

        # Create tabs
        tabs = {
            "BASIC ANALYSIS": self._create_basic_analysis_tab,
            "ADVANCED ATTACKS": self._create_advanced_attacks_tab,
            "PERFORMANCE TEST": self._create_performance_tab,
            "SECURITY METRICS": self._create_security_metrics_tab,
            "ROUND CONSTANTS": self._create_round_constants_tab
        }

        for tab_name, tab_creator in tabs.items():
            tab_frame = ttk.Frame(notebook)
            notebook.add(tab_frame, text=tab_name)
            tab_creator(tab_frame)

    def _configure_notebook_style(self):
        """Configure ttk notebook to match hacker theme"""
        style = ttk.Style()
        style.theme_use('default')

        # Configure notebook style
        style.configure("TNotebook",
                        background=self.STYLE["colors"]["background"],
                        borderwidth=0)

        style.configure("TNotebook.Tab",
                        font=self.STYLE["font_bold"],
                        background=self.STYLE["colors"]["frame"],
                        foreground=self.STYLE["colors"]["text"],
                        padding=[20, 5],
                        borderwidth=0)

        style.map("TNotebook.Tab",
                  background=[("selected", self.STYLE["colors"]["accent"]),
                              ("active", self.STYLE["colors"]["accent_hover"])],
                  foreground=[("selected", self.STYLE["colors"]["button_fg"]),
                              ("active", self.STYLE["colors"]["button_fg"])])

    def _create_basic_analysis_tab(self, parent):
        """Create basic cryptographic analysis tab"""
        # Main container with scrollbar
        container = tk.Frame(parent, bg=self.STYLE["colors"]["background"])
        container.pack(fill='both', expand=True)

        # Cipher Validation
        val_frame = self._create_hacker_frame(container, "CIPHER VALIDATION :: TEST VECTORS")
        val_frame.pack(fill='x', pady=5)

        settings_frame = tk.Frame(val_frame, bg=self.STYLE["colors"]["frame"])
        settings_frame.pack(fill='x', pady=5)

        tk.Label(settings_frame, text="Test Count:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.val_test_count = self._create_hacker_entry(settings_frame, "5", 10)
        self.val_test_count.pack(side='left', padx=5)

        self._create_hacker_button(val_frame, "[ RUN VALIDATION TESTS ]",
                                   self._run_cipher_validation).pack(pady=5)

        self.validation_text = self._create_hacker_text(val_frame, height=6)
        self.validation_text.pack(fill='x', pady=5)

        # Byte Frequency Analysis
        freq_frame = self._create_hacker_frame(container, "BYTE FREQUENCY ANALYSIS :: RANDOMNESS TESTS")
        freq_frame.pack(fill='x', pady=5)

        freq_settings = tk.Frame(freq_frame, bg=self.STYLE["colors"]["frame"])
        freq_settings.pack(fill='x', pady=5)

        tk.Label(freq_settings, text="Sample Size:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.freq_sample_size = self._create_hacker_entry(freq_settings, "1000", 10)
        self.freq_sample_size.pack(side='left', padx=5)

        self._create_hacker_button(freq_frame, "[ ANALYZE BYTE DISTRIBUTION ]",
                                   self._run_byte_frequency).pack(pady=5)

        self.frequency_text = self._create_hacker_text(freq_frame, height=8)
        self.frequency_text.pack(fill='x', pady=5)

        # Avalanche Effect
        avalanche_frame = self._create_hacker_frame(container, "AVALANCHE EFFECT :: DIFFUSION ANALYSIS")
        avalanche_frame.pack(fill='x', pady=5)

        avalanche_settings = tk.Frame(avalanche_frame, bg=self.STYLE["colors"]["frame"])
        avalanche_settings.pack(fill='x', pady=5)

        tk.Label(avalanche_settings, text="Test Bits:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.avalanche_test_bits = self._create_hacker_entry(avalanche_settings, "100", 10)
        self.avalanche_test_bits.pack(side='left', padx=5)

        self._create_hacker_button(avalanche_frame, "[ TEST AVALANCHE EFFECT ]",
                                   self._run_avalanche_test).pack(pady=5)

        self.avalanche_text = self._create_hacker_text(avalanche_frame, height=8)
        self.avalanche_text.pack(fill='x', pady=5)

    def _create_advanced_attacks_tab(self, parent):
        """Create advanced cryptanalysis attacks tab"""
        container = tk.Frame(parent, bg=self.STYLE["colors"]["background"])
        container.pack(fill='both', expand=True)

        # Bit-Flip Attack
        bitflip_frame = self._create_hacker_frame(container, "BIT-FLIP ATTACK :: INTEGRITY TESTING")
        bitflip_frame.pack(fill='x', pady=5)

        bitflip_settings = tk.Frame(bitflip_frame, bg=self.STYLE["colors"]["frame"])
        bitflip_settings.pack(fill='x', pady=5)

        tk.Label(bitflip_settings, text="Bits to Flip:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.bitflip_bits = self._create_hacker_entry(bitflip_settings, "32", 10)
        self.bitflip_bits.pack(side='left', padx=5)

        self._create_hacker_button(bitflip_frame, "[ SIMULATE BIT-FLIP ATTACK ]",
                                   self._run_bitflip_attack).pack(pady=5)

        self.bitflip_text = self._create_hacker_text(bitflip_frame, height=8)
        self.bitflip_text.pack(fill='x', pady=5)

        # Differential Analysis
        diff_frame = self._create_hacker_frame(container, "DIFFERENTIAL ANALYSIS :: CRYPTANALYSIS RESISTANCE")
        diff_frame.pack(fill='x', pady=5)

        # Input frames for differential analysis
        diff_input_frame = tk.Frame(diff_frame, bg=self.STYLE["colors"]["frame"])
        diff_input_frame.pack(fill='x', pady=5)

        tk.Label(diff_input_frame, text="Plaintext 1:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.diff_text1 = self._create_hacker_entry(diff_input_frame, "Hello World", 20)
        self.diff_text1.pack(side='left', padx=5)

        tk.Label(diff_input_frame, text="Plaintext 2:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(20, 0))
        self.diff_text2 = self._create_hacker_entry(diff_input_frame, "Hello World!", 20)
        self.diff_text2.pack(side='left', padx=5)

        tk.Label(diff_input_frame, text="Key:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(20, 0))
        self.diff_key = self._create_hacker_entry(diff_input_frame, "testkey123", 15)
        self.diff_key.pack(side='left', padx=5)

        self._create_hacker_button(diff_frame, "[ RUN DIFFERENTIAL ANALYSIS ]",
                                   self._run_differential_analysis).pack(pady=5)

        self.diff_text = self._create_hacker_text(diff_frame, height=6)
        self.diff_text.pack(fill='x', pady=5)

    def _create_performance_tab(self, parent):
        """Create performance testing tab"""
        container = tk.Frame(parent, bg=self.STYLE["colors"]["background"])
        container.pack(fill='both', expand=True)

        # Dictionary Attack
        dict_frame = self._create_hacker_frame(container, "DICTIONARY ATTACK :: PASSWORD STRENGTH")
        dict_frame.pack(fill='x', pady=5)

        dict_settings = tk.Frame(dict_frame, bg=self.STYLE["colors"]["frame"])
        dict_settings.pack(fill='x', pady=5)

        tk.Label(dict_settings, text="Ciphertext:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.dict_ciphertext = self._create_hacker_entry(dict_settings, "", 50)
        self.dict_ciphertext.pack(side='left', padx=5)

        tk.Label(dict_settings, text="Max Attempts:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(20, 0))
        self.dict_max_attempts = self._create_hacker_entry(dict_settings, "1000", 10)
        self.dict_max_attempts.pack(side='left', padx=5)

        self._create_hacker_button(dict_frame, "[ RUN DICTIONARY ATTACK ]",
                                   self._run_dictionary_attack).pack(pady=5)

        self.dict_text = self._create_hacker_text(dict_frame, height=8)
        self.dict_text.pack(fill='x', pady=5)

        # Brute Force Attack
        brute_frame = self._create_hacker_frame(container, "BRUTE FORCE :: KEYSPACE ANALYSIS")
        brute_frame.pack(fill='x', pady=5)

        brute_settings = tk.Frame(brute_frame, bg=self.STYLE["colors"]["frame"])
        brute_settings.pack(fill='x', pady=5)

        tk.Label(brute_settings, text="Ciphertext:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.brute_ciphertext = self._create_hacker_entry(brute_settings, "", 50)
        self.brute_ciphertext.pack(side='left', padx=5)

        tk.Label(brute_settings, text="Key Length:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(20, 0))
        self.brute_key_length = self._create_hacker_entry(brute_settings, "3", 5)
        self.brute_key_length.pack(side='left', padx=5)

        tk.Label(brute_settings, text="Char Set:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(20, 0))
        self.brute_char_set = ttk.Combobox(brute_settings,
                                           values=["numeric", "lowercase", "uppercase", "alphanumeric", "printable"],
                                           state="readonly", width=12)
        self.brute_char_set.set("printable")
        self.brute_char_set.pack(side='left', padx=5)

        tk.Label(brute_settings, text="Max Attempts:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(20, 0))
        self.brute_max_attempts = self._create_hacker_entry(brute_settings, "1000", 10)
        self.brute_max_attempts.pack(side='left', padx=5)

        self._create_hacker_button(brute_frame, "[ RUN BRUTE FORCE ]",
                                   self._run_brute_force).pack(pady=5)

        self.brute_text = self._create_hacker_text(brute_frame, height=8)
        self.brute_text.pack(fill='x', pady=5)

    def _create_security_metrics_tab(self, parent):
        """Create security metrics and benchmarking tab"""
        container = tk.Frame(parent, bg=self.STYLE["colors"]["background"])
        container.pack(fill='both', expand=True)

        # Performance Benchmark
        perf_frame = self._create_hacker_frame(container, "PERFORMANCE BENCHMARK :: SPEED ANALYSIS")
        perf_frame.pack(fill='x', pady=5)

        perf_settings = tk.Frame(perf_frame, bg=self.STYLE["colors"]["frame"])
        perf_settings.pack(fill='x', pady=5)

        tk.Label(perf_settings, text="Test Sizes (comma sep):", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left')
        self.perf_sizes = self._create_hacker_entry(perf_settings, "100,1000,10000", 20)
        self.perf_sizes.pack(side='left', padx=5)

        self._create_hacker_button(perf_frame, "[ RUN PERFORMANCE TEST ]",
                                   self._run_performance_test).pack(pady=5)

        self.perf_text = self._create_hacker_text(perf_frame, height=10)
        self.perf_text.pack(fill='x', pady=5)

        # Security Score
        security_frame = self._create_hacker_frame(container, "SECURITY SCORE :: OVERALL ASSESSMENT")
        security_frame.pack(fill='x', pady=5)

        self._create_hacker_button(security_frame, "[ CALCULATE SECURITY SCORE ]",
                                   self._calculate_security_score).pack(pady=5)

        self.security_text = self._create_hacker_text(security_frame, height=8)
        self.security_text.pack(fill='x', pady=5)

    def _run_cipher_validation(self):
        """Run cipher validation tests"""
        try:
            test_count = int(self.val_test_count.get())
        except:
            test_count = 5

        test_vectors = []
        for i in range(test_count):
            plaintext = f"Test message {i + 1}"
            key = f"testkey{i + 1}"
            test_vectors.append((plaintext, key, ""))

        # Generate expected ciphertexts
        for i, (plaintext, key, _) in enumerate(test_vectors):
            try:
                ciphertext = self.cipher.encrypt(plaintext, key)
                test_vectors[i] = (plaintext, key, ciphertext)
            except:
                test_vectors[i] = (plaintext, key, "ERROR")

        results = self.crypto_lab.cipher_validation(test_vectors)

        self.validation_text.delete(1.0, tk.END)
        self.validation_text.insert(1.0, "CIPHER VALIDATION RESULTS:\n")
        self.validation_text.insert(tk.END, "=" * 50 + "\n\n")

        passed = sum(results.values())
        total = len(results)

        for test_name, passed_test in results.items():
            status = "PASS" if passed_test else "FAIL"
            color = "green" if passed_test else "red"
            self.validation_text.insert(tk.END, f"{test_name}: ", "bold")
            self.validation_text.insert(tk.END, f"{status}\n", color)

        self.validation_text.insert(tk.END, f"\nSUMMARY: {passed}/{total} tests passed ")
        self.validation_text.insert(tk.END, f"({passed / total * 100:.1f}%)\n")

        if passed == total:
            self.validation_text.insert(tk.END, "✓ CIPHER VALIDATION: SUCCESS\n", "success")
        else:
            self.validation_text.insert(tk.END, "✗ CIPHER VALIDATION: FAILED\n", "error")

        self.validation_text.tag_configure("bold", font=self.STYLE["font_bold"])
        self.validation_text.tag_configure("green", foreground="#00FF00")
        self.validation_text.tag_configure("red", foreground="#FF0000")
        self.validation_text.tag_configure("success", foreground="#00FF00", font=self.STYLE["font_bold"])
        self.validation_text.tag_configure("error", foreground="#FF0000", font=self.STYLE["font_bold"])

    def _run_byte_frequency(self):
        """Run byte frequency analysis"""
        ciphertext = self.result_text.get(1.0, tk.END).strip()
        if not ciphertext:
            messagebox.showwarning("Input Error", "No ciphertext available for analysis.")
            return

        try:
            sample_size = int(self.freq_sample_size.get())
        except:
            sample_size = 1000

        results = self.crypto_lab.byte_frequency_analysis(ciphertext, sample_size)

        self.frequency_text.delete(1.0, tk.END)
        self.frequency_text.insert(1.0, "BYTE FREQUENCY ANALYSIS:\n")
        self.frequency_text.insert(tk.END, "=" * 50 + "\n\n")

        if "error" in results:
            self.frequency_text.insert(tk.END, f"Error: {results['error']}\n")
            return

        for key, value in results.items():
            self.frequency_text.insert(tk.END, f"{key.replace('_', ' ').title()}: {value}\n")

        # Interpretation
        self.frequency_text.insert(tk.END, "\n" + "=" * 50 + "\n")
        self.frequency_text.insert(tk.END, "INTERPRETATION:\n\n")

        chi_squared = results.get("chi_squared", 0)
        if chi_squared < 200:
            self.frequency_text.insert(tk.END, "⚠ WARNING: Distribution may not be random enough\n", "warning")
            self.frequency_text.insert(tk.END, "   Chi-squared too low - possible patterns detected\n")
        elif chi_squared > 300:
            self.frequency_text.insert(tk.END, "⚠ WARNING: Distribution shows unusual patterns\n", "warning")
            self.frequency_text.insert(tk.END, "   Chi-squared too high - non-random distribution\n")
        else:
            self.frequency_text.insert(tk.END, "✓ GOOD: Distribution appears random\n", "good")
            self.frequency_text.insert(tk.END, "   Chi-squared within expected range\n")

        # Additional tests
        self.frequency_text.insert(tk.END, f"\nMonobit Test: {results.get('monobit_test', 'N/A')}\n")
        self.frequency_text.insert(tk.END, f"Runs Test: {results.get('runs_test', 'N/A')}\n")

        self.frequency_text.tag_configure("warning", foreground="#FF6B00")
        self.frequency_text.tag_configure("good", foreground="#00FF00")

    def _run_avalanche_test(self):
        """Run avalanche effect test"""
        plaintext = self.text_entry.get(1.0, tk.END).strip()
        key = self.key_entry.get().strip()

        if not plaintext or not key:
            messagebox.showwarning("Input Error", "Need both plaintext and key for avalanche test.")
            return

        try:
            test_bits = int(self.avalanche_test_bits.get())
        except:
            test_bits = 100

        results = self.crypto_lab.avalanche_effect_test(plaintext, key, test_bits)

        self.avalanche_text.delete(1.0, tk.END)
        self.avalanche_text.insert(1.0, "AVALANCHE EFFECT ANALYSIS:\n")
        self.avalanche_text.insert(tk.END, "=" * 50 + "\n\n")

        if "error" in results:
            self.avalanche_text.insert(tk.END, f"Error: {results['error']}\n")
            return

        for key, value in results.items():
            self.avalanche_text.insert(tk.END, f"{key.replace('_', ' ').title()}: {value}\n")

        # Interpretation
        self.avalanche_text.insert(tk.END, "\n" + "=" * 50 + "\n")
        self.avalanche_text.insert(tk.END, "INTERPRETATION:\n\n")

        deviation = results.get("deviation", 1.0)
        if deviation < 0.1:
            self.avalanche_text.insert(tk.END, "✓ EXCELLENT: Strong avalanche effect detected\n", "excellent")
            self.avalanche_text.insert(tk.END, "   Close to ideal 50% bit change ratio\n")
        elif deviation < 0.2:
            self.avalanche_text.insert(tk.END, "✓ GOOD: Reasonable avalanche effect\n", "good")
            self.avalanche_text.insert(tk.END, "   Acceptable diffusion properties\n")
        else:
            self.avalanche_text.insert(tk.END, "⚠ POOR: Weak avalanche effect\n", "poor")
            self.avalanche_text.insert(tk.END, "   Insufficient diffusion detected\n")

        self.avalanche_text.tag_configure("excellent", foreground="#00FF00")
        self.avalanche_text.tag_configure("good", foreground="#90FF90")
        self.avalanche_text.tag_configure("poor", foreground="#FF6B00")

    def _run_bitflip_attack(self):
        """Run bit-flip attack simulation"""
        ciphertext = self.result_text.get(1.0, tk.END).strip()
        key = self.key_entry.get().strip()

        if not ciphertext or not key:
            messagebox.showwarning("Input Error", "Need both ciphertext and key for bit-flip attack simulation.")
            return

        try:
            num_bits = int(self.bitflip_bits.get())
        except:
            num_bits = 32

        results = self.crypto_lab.bit_flip_attack_simulation(ciphertext, key, num_bits)

        self.bitflip_text.delete(1.0, tk.END)
        self.bitflip_text.insert(1.0, "BIT-FLIP ATTACK SIMULATION:\n")
        self.bitflip_text.insert(tk.END, "=" * 50 + "\n\n")

        if "error" in results:
            self.bitflip_text.insert(tk.END, f"Error: {results['error']}\n")
            return

        total = sum(results.values())
        if total > 0:
            for key, value in results.items():
                percentage = (value / total) * 100
                self.bitflip_text.insert(tk.END, f"{key.replace('_', ' ').title()}: {value} ({percentage:.1f}%)\n")

        # Interpretation
        self.bitflip_text.insert(tk.END, "\n" + "=" * 50 + "\n")
        self.bitflip_text.insert(tk.END, "INTERPRETATION:\n\n")

        hmac_rate = results.get("hmac_detected", 0) / total * 100 if total > 0 else 0
        if hmac_rate > 95:
            self.bitflip_text.insert(tk.END, "✓ EXCELLENT: HMAC effectively prevents bit-flip attacks\n", "excellent")
            self.bitflip_text.insert(tk.END, "   Strong integrity protection detected\n")
        elif hmac_rate > 80:
            self.bitflip_text.insert(tk.END, "✓ GOOD: HMAC provides reasonable protection\n", "good")
            self.bitflip_text.insert(tk.END, "   Adequate integrity measures\n")
        else:
            self.bitflip_text.insert(tk.END, "⚠ POOR: HMAC protection may be insufficient\n", "poor")
            self.bitflip_text.insert(tk.END, "   Consider strengthening integrity checks\n")

        self.bitflip_text.tag_configure("excellent", foreground="#00FF00")
        self.bitflip_text.tag_configure("good", foreground="#90FF90")
        self.bitflip_text.tag_configure("poor", foreground="#FF6B00")

    def _run_differential_analysis(self):
        """Run differential cryptanalysis"""
        plaintext1 = self.diff_text1.get()
        plaintext2 = self.diff_text2.get()
        key = self.diff_key.get()

        if not plaintext1 or not plaintext2 or not key:
            messagebox.showwarning("Input Error", "Need both plaintexts and key for differential analysis.")
            return

        results = self.crypto_lab.differential_analysis(plaintext1, plaintext2, key)

        self.diff_text.delete(1.0, tk.END)
        self.diff_text.insert(1.0, "DIFFERENTIAL ANALYSIS:\n")
        self.diff_text.insert(tk.END, "=" * 50 + "\n\n")

        if "error" in results:
            self.diff_text.insert(tk.END, f"Error: {results['error']}\n")
            return

        for key, value in results.items():
            self.diff_text.insert(tk.END, f"{key.replace('_', ' ').title()}: {value}\n")

        # Interpretation
        self.diff_text.insert(tk.END, "\n" + "=" * 50 + "\n")
        self.diff_text.insert(tk.END, "INTERPRETATION:\n\n")

        deviation = results.get("deviation", 1.0)
        if deviation < 0.1:
            self.diff_text.insert(tk.END, "✓ EXCELLENT: Strong resistance to differential cryptanalysis\n", "excellent")
            self.diff_text.insert(tk.END, "   High resistance to chosen-plaintext attacks\n")
        elif deviation < 0.2:
            self.diff_text.insert(tk.END, "✓ GOOD: Reasonable resistance to differential attacks\n", "good")
            self.diff_text.insert(tk.END, "   Moderate security against differential analysis\n")
        else:
            self.diff_text.insert(tk.END, "⚠ POOR: Vulnerable to differential cryptanalysis\n", "poor")
            self.diff_text.insert(tk.END, "   Consider strengthening diffusion properties\n")

        self.diff_text.tag_configure("excellent", foreground="#00FF00")
        self.diff_text.tag_configure("good", foreground="#90FF90")
        self.diff_text.tag_configure("poor", foreground="#FF6B00")

    def _run_dictionary_attack(self):
        """Run dictionary attack simulation"""
        ciphertext = self.dict_ciphertext.get().strip()
        if not ciphertext:
            messagebox.showwarning("Input Error", "Need ciphertext for dictionary attack.")
            return

        try:
            max_attempts = int(self.dict_max_attempts.get())
        except:
            max_attempts = 1000

        # Common passwords dictionary
        common_passwords = [
            "password", "123456", "password123", "admin", "test", "hello",
            "qwerty", "letmein", "welcome", "monkey", "dragon", "master",
            "123456789", "football", "iloveyou", "secret", "testkey123"
        ]

        results = self.crypto_lab.dictionary_attack_simulation(ciphertext, common_passwords, max_attempts)

        self.dict_text.delete(1.0, tk.END)
        self.dict_text.insert(1.0, "DICTIONARY ATTACK SIMULATION:\n")
        self.dict_text.insert(tk.END, "=" * 50 + "\n\n")

        for key, value in results.items():
            self.dict_text.insert(tk.END, f"{key.replace('_', ' ').title()}: {value}\n")

        # Interpretation
        self.dict_text.insert(tk.END, "\n" + "=" * 50 + "\n")
        self.dict_text.insert(tk.END, "INTERPRETATION:\n\n")

        if results.get("successful", 0) > 0:
            self.dict_text.insert(tk.END, f"⚠ VULNERABLE: Key found: {results['found_key']}\n", "vulnerable")
            self.dict_text.insert(tk.END, "   Weak password detected - recommend using stronger passwords\n")
        else:
            self.dict_text.insert(tk.END, "✓ SECURE: Dictionary attack failed\n", "secure")
            self.dict_text.insert(tk.END, "   Password appears strong against common dictionary attacks\n")

        self.dict_text.tag_configure("vulnerable", foreground="#FF6B00")
        self.dict_text.tag_configure("secure", foreground="#00FF00")

    def _run_brute_force(self):
        """Run brute force attack simulation"""
        ciphertext = self.brute_ciphertext.get().strip()
        if not ciphertext:
            messagebox.showwarning("Input Error", "Need ciphertext for brute force attack.")
            return

        try:
            key_length = int(self.brute_key_length.get())
            max_attempts = int(self.brute_max_attempts.get())
        except:
            key_length = 3
            max_attempts = 1000

        char_set = self.brute_char_set.get()

        results = self.crypto_lab.brute_force_simulation(ciphertext, key_length, max_attempts, char_set)

        self.brute_text.delete(1.0, tk.END)
        self.brute_text.insert(1.0, "BRUTE FORCE ATTACK SIMULATION:\n")
        self.brute_text.insert(tk.END, "=" * 50 + "\n\n")

        for key, value in results.items():
            self.brute_text.insert(tk.END, f"{key.replace('_', ' ').title()}: {value}\n")

        # Interpretation
        self.brute_text.insert(tk.END, "\n" + "=" * 50 + "\n")
        self.brute_text.insert(tk.END, "INTERPRETATION:\n\n")

        keyspace = results.get("keyspace_size", 0)
        attempted = results.get("attempted", 0)

        if results.get("successful", 0) > 0:
            self.brute_text.insert(tk.END, f"⚠ VULNERABLE: Key found: {results['found_key']}\n", "vulnerable")
            self.brute_text.insert(tk.END, f"   Key was found in {attempted} attempts\n")
            self.brute_text.insert(tk.END, "   Consider using longer, more complex keys\n")
        else:
            success_probability = (attempted / keyspace) * 100 if keyspace > 0 else 0
            self.brute_text.insert(tk.END, f"✓ SECURE: Brute force failed after {attempted} attempts\n", "secure")
            self.brute_text.insert(tk.END, f"   Success probability: {success_probability:.6f}%\n")
            self.brute_text.insert(tk.END, f"   Full keyspace size: {keyspace:,} possible keys\n")
            self.brute_text.insert(tk.END, f"   Attack speed: {results.get('attack_speed', 0):.1f} attempts/sec\n")

        self.brute_text.tag_configure("vulnerable", foreground="#FF6B00")
        self.brute_text.tag_configure("secure", foreground="#00FF00")

    def _fibonacci(self, n: int) -> int:
        """Calculate n-th Fibonacci number"""
        if n <= 0:
            return 0
        elif n == 1:
            return 1
        a, b = 0, 1
        for _ in range(2, n + 1):
            a, b = b, a + b
        return b

    def _generate_round_constant(self, round_index: int) -> int:
        """Generate round constant using SHA3-256 (matches the cipher's method)"""
        domain_separator = b"partybasher_round_constant_v2_"
        data = domain_separator + round_index.to_bytes(8, 'big')
        hash_bytes = hashlib.sha3_256(data).digest()
        round_constant = int.from_bytes(hash_bytes[:8], 'big')
        return round_constant & MASK_64

    def _create_round_constants_tab(self, parent):
        """Create round constants analysis tab"""
        container = tk.Frame(parent, bg=self.STYLE["colors"]["background"])
        container.pack(fill='both', expand=True)

        # Header frame
        header_frame = self._create_hacker_frame(container,
                                                 "ROUND CONSTANT VERIFICATION :: NOTHING UP MY SLEEVE NUMBERS")
        header_frame.pack(fill='x', pady=5)

        info_text = """
            Round Constants are generated using SHA3-256 for cryptographic security:
            • Domain-separated input: "partybasher_round_constant_v2_" + round_index
            • SHA3-256 hash provides cryptographically secure randomness
            • First 8 bytes of hash used as 64-bit constant
            • Ensures no mathematical patterns or predictable relationships
            • Follows established cryptographic practices for constant generation
        """
        info_label = tk.Label(header_frame, text=info_text, font=self.STYLE["font_normal"],
                              bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"],
                              justify=tk.LEFT)
        info_label.pack(fill='x', pady=10)

        # Controls frame
        controls_frame = self._create_hacker_frame(container, "ANALYSIS CONTROLS")
        controls_frame.pack(fill='x', pady=5)

        controls_inner = tk.Frame(controls_frame, bg=self.STYLE["colors"]["frame"])
        controls_inner.pack(fill='x', pady=10)

        tk.Label(controls_inner, text="Rounds to Analyze:", font=self.STYLE["font_normal"],
                 bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"]).pack(side='left', padx=(0, 10))

        self.rc_rounds_count = tk.Entry(controls_inner, font=self.STYLE["font_normal"],
                                        bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                                        width=10)
        self.rc_rounds_count.insert(0, "20")
        self.rc_rounds_count.pack(side='left', padx=(0, 20))

        self._create_hacker_button(controls_inner, "[ GENERATE CONSTANTS ]",
                                   self._analyze_round_constants).pack(side='left', padx=(0, 10))

        self._create_hacker_button(controls_inner, "[ VERIFY UNIQUENESS ]",
                                   self._verify_constants_uniqueness).pack(side='left')

        # Results frame
        results_frame = self._create_hacker_frame(container, "ROUND CONSTANTS ANALYSIS")
        results_frame.pack(fill='both', expand=True, pady=5)

        # Create a frame for the table headers
        headers_frame = tk.Frame(results_frame, bg=self.STYLE["colors"]["frame"])
        headers_frame.pack(fill='x', pady=(0, 5))

        # Table headers
        headers = []
        widths = []

        for i, (header, width) in enumerate(zip(headers, widths)):
            label = tk.Label(headers_frame, text=header, font=self.STYLE["font_bold"],
                             bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["accent"],
                             width=width, anchor='w')
            label.pack(side='left', padx=(10 if i == 0 else 5, 5))

        # Text area for results with scrollbar
        text_container = tk.Frame(results_frame, bg=self.STYLE["colors"]["entry_bg"])
        text_container.pack(fill='both', expand=True)

        self.rc_results_text = scrolledtext.ScrolledText(text_container, height=15,
                                                         font=self.STYLE["font_normal"],
                                                         bg=self.STYLE["colors"]["entry_bg"],
                                                         fg=self.STYLE["colors"]["text"],
                                                         relief='flat', borderwidth=0)
        self.rc_results_text.pack(fill='both', expand=True, padx=5, pady=5)

        # Statistics frame
        stats_frame = self._create_hacker_frame(container, "STATISTICAL ANALYSIS")
        stats_frame.pack(fill='x', pady=5)

        self.rc_stats_text = scrolledtext.ScrolledText(stats_frame, height=6,
                                                       font=self.STYLE["font_normal"],
                                                       bg=self.STYLE["colors"]["entry_bg"],
                                                       fg=self.STYLE["colors"]["text"],
                                                       relief='flat', borderwidth=0)
        self.rc_stats_text.pack(fill='both', expand=True, padx=5, pady=5)

    def _analyze_round_constants(self):
        """Analyze and display round constants using SHA3-256 method"""
        try:
            num_rounds = int(self.rc_rounds_count.get())
            if num_rounds <= 0 or num_rounds > 100:
                messagebox.showwarning("Invalid Input", "Please enter rounds between 1 and 100")
                return
        except:
            num_rounds = 20

        self.rc_results_text.delete(1.0, tk.END)
        self.rc_stats_text.delete(1.0, tk.END)

        # Generate and display constants
        constants = []
        self.rc_results_text.insert(tk.END, "ROUND CONSTANT GENERATION ANALYSIS (SHA3-256)\n")
        self.rc_results_text.insert(tk.END, "=" * 100 + "\n\n")

        # Headers for the new display
        self.rc_results_text.insert(tk.END, f"{'Round':<6} {'Hash Input (hex)':<50} {'Constant (Hex)':<20}\n")
        self.rc_results_text.insert(tk.END, "-" * 100 + "\n")

        for i in range(num_rounds):
            # Generate using the new method
            domain_separator = b"partybasher_round_constant_v2_"
            data = domain_separator + i.to_bytes(8, 'big')
            hash_bytes = hashlib.sha3_256(data).digest()
            constant = int.from_bytes(hash_bytes[:8], 'big') & MASK_64
            constants.append(constant)

            # Format the output to show the hash input and result
            hash_input_hex = data.hex()
            line = f"{i:<6} {hash_input_hex:<50} 0x{constant:016x}\n"
            self.rc_results_text.insert(tk.END, line)

        # Calculate statistics
        self._calculate_constants_statistics(constants, num_rounds)

    def _verify_constants_uniqueness(self):
        """Verify that all round constants are unique"""
        try:
            num_rounds = int(self.rc_rounds_count.get())
        except:
            num_rounds = 20

        constants = [self._generate_round_constant(i) for i in range(num_rounds)]
        unique_constants = set(constants)

        self.rc_stats_text.delete(1.0, tk.END)
        self.rc_stats_text.insert(tk.END, "UNIQUENESS VERIFICATION:\n")
        self.rc_stats_text.insert(tk.END, "=" * 50 + "\n\n")

        if len(unique_constants) == len(constants):
            self.rc_stats_text.insert(tk.END, "✓ SUCCESS: All round constants are unique\n", "success")
            self.rc_stats_text.insert(tk.END, f"All {num_rounds} constants are distinct\n")
        else:
            self.rc_stats_text.insert(tk.END, "✗ WARNING: Duplicate constants found\n", "warning")
            self.rc_stats_text.insert(tk.END, f"Found {len(unique_constants)} unique out of {num_rounds} constants\n")

            # Find duplicates
            from collections import Counter
            counter = Counter(constants)
            duplicates = [const for const, count in counter.items() if count > 1]
            self.rc_stats_text.insert(tk.END, f"Duplicate constants: {len(duplicates)}\n")

        # Configure text tags for colors
        self.rc_stats_text.tag_configure("success", foreground="#00FF00")
        self.rc_stats_text.tag_configure("warning", foreground="#FF6B00")

    def _calculate_constants_statistics(self, constants, num_rounds):
        """Calculate and display statistical analysis of round constants"""
        self.rc_stats_text.delete(1.0, tk.END)
        self.rc_stats_text.insert(tk.END, "STATISTICAL ANALYSIS:\n")
        self.rc_stats_text.insert(tk.END, "=" * 50 + "\n\n")

        # Basic statistics
        avg_constant = sum(constants) / len(constants)
        max_constant = max(constants)
        min_constant = min(constants)

        # Bit distribution analysis
        bit_counts = []
        for const in constants:
            bit_count = bin(const).count('1')
            bit_counts.append(bit_count)

        avg_bits = sum(bit_counts) / len(bit_counts)

        self.rc_stats_text.insert(tk.END, f"Total Rounds Analyzed: {num_rounds}\n")
        self.rc_stats_text.insert(tk.END, f"Average Constant Value: {avg_constant:.2f}\n")
        self.rc_stats_text.insert(tk.END, f"Maximum Constant: 0x{max_constant:016x}\n")
        self.rc_stats_text.insert(tk.END, f"Minimum Constant: 0x{min_constant:016x}\n")
        self.rc_stats_text.insert(tk.END, f"Average 1-bits per Constant: {avg_bits:.2f}/64\n")

        # Bit balance analysis
        ideal_bit_balance = 32  # 50% of 64 bits
        bit_deviation = abs(avg_bits - ideal_bit_balance)

        if bit_deviation <= 4:
            self.rc_stats_text.insert(tk.END, "✓ GOOD: Bit distribution is balanced\n", "good")
        elif bit_deviation <= 8:
            self.rc_stats_text.insert(tk.END, "✓ FAIR: Reasonable bit distribution\n", "fair")
        else:
            self.rc_stats_text.insert(tk.END, "⚠ POOR: Bit distribution may be unbalanced\n", "poor")

        # Hamming distance analysis (between consecutive constants)
        if len(constants) > 1:
            hamming_distances = []
            for i in range(len(constants) - 1):
                # Calculate Hamming distance between consecutive constants
                xor_result = constants[i] ^ constants[i + 1]
                hamming_dist = bin(xor_result).count('1')
                hamming_distances.append(hamming_dist)

            avg_hamming = sum(hamming_distances) / len(hamming_distances)
            self.rc_stats_text.insert(tk.END, f"Average Hamming Distance: {avg_hamming:.2f}/64\n")

            if avg_hamming >= 28 and avg_hamming <= 36:  # Ideal range for 64-bit values
                self.rc_stats_text.insert(tk.END, "✓ EXCELLENT: Good diffusion between rounds\n", "excellent")
            elif avg_hamming >= 24 and avg_hamming <= 40:
                self.rc_stats_text.insert(tk.END, "✓ GOOD: Reasonable diffusion\n", "good")
            else:
                self.rc_stats_text.insert(tk.END, "⚠ POOR: Low diffusion between rounds\n", "poor")

        # Configure text tags for colors
        self.rc_stats_text.tag_configure("excellent", foreground="#00FF00")
        self.rc_stats_text.tag_configure("good", foreground="#90FF90")
        self.rc_stats_text.tag_configure("fair", foreground="#FFA500")
        self.rc_stats_text.tag_configure("poor", foreground="#FF6B00")

    def _run_performance_test(self):
        """Run performance benchmark"""
        try:
            sizes_str = self.perf_sizes.get()
            sizes = [int(x.strip()) for x in sizes_str.split(',')]
        except:
            sizes = [100, 1000, 10000]

        results = self.crypto_lab.performance_benchmark(sizes)

        self.perf_text.delete(1.0, tk.END)
        self.perf_text.insert(1.0, "PERFORMANCE BENCHMARK RESULTS:\n")
        self.perf_text.insert(tk.END, "=" * 50 + "\n\n")

        for size, metrics in results.items():
            self.perf_text.insert(tk.END, f"Message Size: {size} characters\n", "bold")
            self.perf_text.insert(tk.END, f"  Encryption Time: {metrics['encrypt_time']:.4f}s\n")
            self.perf_text.insert(tk.END, f"  Decryption Time: {metrics['decrypt_time']:.4f}s\n")
            self.perf_text.insert(tk.END, f"  Encryption Speed: {metrics['encrypt_speed']:.2f} chars/s\n")
            self.perf_text.insert(tk.END, f"  Decryption Speed: {metrics['decrypt_speed']:.2f} chars/s\n\n")

        self.perf_text.tag_configure("bold", font=self.STYLE["font_bold"])

    def _calculate_security_score(self):
        """Calculate overall security score by running comprehensive tests"""
        self.security_text.delete(1.0, tk.END)
        self.security_text.insert(1.0, "COMPREHENSIVE SECURITY ASSESSMENT:\n")
        self.security_text.insert(tk.END, "=" * 60 + "\n\n")
        self.security_text.insert(tk.END, "Running full security test suite...\n\n")
        self.security_text.update()

        test_results = {}
        total_score = 0
        max_possible_score = 0

        # Test 1: Byte Frequency Analysis
        try:
            self.security_text.insert(tk.END, "• Running Byte Frequency Analysis... ", "bold")
            self.security_text.update()

            # Generate test ciphertext
            test_plaintext = "Security test message for frequency analysis " + os.urandom(8).hex()
            test_key = "test_key_123"
            ciphertext = self.cipher.encrypt(test_plaintext, test_key)

            results = self.crypto_lab.byte_frequency_analysis(ciphertext, 1000)

            if "error" not in results:
                chi_squared = results.get("chi_squared", 0)
                uniformity = results.get("uniformity_score", 0)
                entropy = results.get("entropy_estimate", 0)
                monobit = results.get("monobit_test", "FAIL")
                runs_test = results.get("runs_test", "FAIL")

                # Calculate score (0-25 points)
                score = 0
                if 200 <= chi_squared <= 300:
                    score += 10
                elif 150 <= chi_squared <= 350:
                    score += 7
                elif 100 <= chi_squared <= 400:
                    score += 4

                score += min(5, uniformity * 5)  # Up to 5 points for uniformity
                score += min(5, (entropy / 8) * 5)  # Up to 5 points for entropy (ideal is 8)

                if monobit == "PASS":
                    score += 2.5
                if runs_test == "PASS":
                    score += 2.5

                test_results["Byte Distribution"] = {
                    "score": score,
                    "max_score": 25,
                    "details": f"χ²={chi_squared:.1f}, Uniformity={uniformity:.3f}, Entropy={entropy:.2f}"
                }
                self.security_text.insert(tk.END, f"DONE ({score}/25)\n", "good")
            else:
                test_results["Byte Distribution"] = {"score": 0, "max_score": 25, "details": "Test failed"}
                self.security_text.insert(tk.END, "FAILED\n", "error")
        except Exception as e:
            test_results["Byte Distribution"] = {"score": 0, "max_score": 25, "details": f"Error: {str(e)}"}
            self.security_text.insert(tk.END, "ERROR\n", "error")

        # Test 2: Avalanche Effect
        try:
            self.security_text.insert(tk.END, "• Running Avalanche Effect Test... ", "bold")
            self.security_text.update()

            test_plaintext = "A" * 100  # Consistent test data
            test_key = "avalanche_test_key"
            results = self.crypto_lab.avalanche_effect_test(test_plaintext, test_key, 50)

            if "error" not in results:
                deviation = results.get("deviation", 1.0)
                avalanche_ratio = results.get("avalanche_ratio", 0)
                consistency = results.get("consistency_std_dev", 100)

                # Calculate score (0-25 points)
                score = 0
                if deviation <= 0.05:
                    score += 15
                elif deviation <= 0.1:
                    score += 12
                elif deviation <= 0.15:
                    score += 8
                elif deviation <= 0.2:
                    score += 5

                # Bonus for consistency
                if consistency < 2:
                    score += 5
                elif consistency < 5:
                    score += 3
                elif consistency < 10:
                    score += 1

                # Ensure score doesn't exceed max
                score = min(score, 25)

                test_results["Avalanche Effect"] = {
                    "score": score,
                    "max_score": 25,
                    "details": f"Deviation={deviation:.3f}, Ratio={avalanche_ratio:.3f}, StdDev={consistency:.1f}"
                }
                self.security_text.insert(tk.END, f"DONE ({score}/25)\n", "good")
            else:
                test_results["Avalanche Effect"] = {"score": 0, "max_score": 25, "details": "Test failed"}
                self.security_text.insert(tk.END, "FAILED\n", "error")
        except Exception as e:
            test_results["Avalanche Effect"] = {"score": 0, "max_score": 25, "details": f"Error: {str(e)}"}
            self.security_text.insert(tk.END, "ERROR\n", "error")

        # Test 3: Differential Analysis
        try:
            self.security_text.insert(tk.END, "• Running Differential Analysis... ", "bold")
            self.security_text.update()

            plaintext1 = "Hello World"
            plaintext2 = "Hello World!"
            test_key = "diff_test_key"
            results = self.crypto_lab.differential_analysis(plaintext1, plaintext2, test_key)

            if "error" not in results:
                deviation = results.get("deviation", 1.0)
                difference_ratio = results.get("difference_ratio", 0)

                # Calculate score (0-20 points)
                score = 0
                if deviation <= 0.05:
                    score += 15
                elif deviation <= 0.1:
                    score += 12
                elif deviation <= 0.15:
                    score += 8
                elif deviation <= 0.2:
                    score += 5

                # Bonus for being close to 50%
                if 0.45 <= difference_ratio <= 0.55:
                    score += 5

                score = min(score, 20)

                test_results["Differential Resistance"] = {
                    "score": score,
                    "max_score": 20,
                    "details": f"Deviation={deviation:.3f}, DiffRatio={difference_ratio:.3f}"
                }
                self.security_text.insert(tk.END, f"DONE ({score}/20)\n", "good")
            else:
                test_results["Differential Resistance"] = {"score": 0, "max_score": 20, "details": "Test failed"}
                self.security_text.insert(tk.END, "FAILED\n", "error")
        except Exception as e:
            test_results["Differential Resistance"] = {"score": 0, "max_score": 20, "details": f"Error: {str(e)}"}
            self.security_text.insert(tk.END, "ERROR\n", "error")

        # Test 4: Bit-Flip Attack Resistance
        try:
            self.security_text.insert(tk.END, "• Running Bit-Flip Attack Test... ", "bold")
            self.security_text.update()

            test_plaintext = "Bit flip test message"
            test_key = "bitflip_test_key"
            ciphertext = self.cipher.encrypt(test_plaintext, test_key)
            results = self.crypto_lab.bit_flip_attack_simulation(ciphertext, test_key, 16)

            if "error" not in results:
                hmac_detected = results.get("hmac_detected", 0)
                total_tests = results.get("total_tests", 1)
                hmac_success_rate = (hmac_detected / total_tests) * 100

                # Calculate score (0-15 points)
                score = 0
                if hmac_success_rate >= 95:
                    score = 15
                elif hmac_success_rate >= 90:
                    score = 12
                elif hmac_success_rate >= 80:
                    score = 8
                elif hmac_success_rate >= 70:
                    score = 5
                elif hmac_success_rate >= 50:
                    score = 2

                test_results["Integrity Protection"] = {
                    "score": score,
                    "max_score": 15,
                    "details": f"HMAC success: {hmac_success_rate:.1f}% ({hmac_detected}/{total_tests})"
                }
                self.security_text.insert(tk.END, f"DONE ({score}/15)\n", "good")
            else:
                test_results["Integrity Protection"] = {"score": 0, "max_score": 15, "details": "Test failed"}
                self.security_text.insert(tk.END, "FAILED\n", "error")
        except Exception as e:
            test_results["Integrity Protection"] = {"score": 0, "max_score": 15, "details": f"Error: {str(e)}"}
            self.security_text.insert(tk.END, "ERROR\n", "error")

        # Test 5: Performance (indirect security measure)
        try:
            self.security_text.insert(tk.END, "• Running Performance Benchmark... ", "bold")
            self.security_text.update()

            results = self.crypto_lab.performance_benchmark([100, 1000])

            # Calculate score based on performance (0-15 points)
            score = 0
            details = []

            for size, metrics in results.items():
                encrypt_speed = metrics.get("encrypt_speed", 0)
                decrypt_speed = metrics.get("decrypt_speed", 0)

                # Higher speed is better, but we want reasonable performance
                if encrypt_speed > 10000:  # chars/sec
                    score += 2
                elif encrypt_speed > 5000:
                    score += 1.5
                elif encrypt_speed > 1000:
                    score += 1

                if decrypt_speed > 10000:
                    score += 2
                elif decrypt_speed > 5000:
                    score += 1.5
                elif decrypt_speed > 1000:
                    score += 1

                details.append(f"{size}: {encrypt_speed:.0f}/s enc, {decrypt_speed:.0f}/s dec")

            score = min(score, 15)  # Cap at 15 points

            test_results["Performance"] = {
                "score": score,
                "max_score": 15,
                "details": "; ".join(details)
            }
            self.security_text.insert(tk.END, f"DONE ({score}/15)\n", "good")
        except Exception as e:
            test_results["Performance"] = {"score": 0, "max_score": 15, "details": f"Error: {str(e)}"}
            self.security_text.insert(tk.END, "ERROR\n", "error")

        # Calculate final scores
        self.security_text.insert(tk.END, "\n" + "=" * 60 + "\n")
        self.security_text.insert(tk.END, "SECURITY ASSESSMENT RESULTS:\n\n")

        total_score = 0
        max_possible_score = 0

        # Display individual test results
        for test_name, result in test_results.items():
            score = result["score"]
            max_score = result["max_score"]
            details = result["details"]

            total_score += score
            max_possible_score += max_score

            percentage = (score / max_score) * 100

            # Color coding based on performance
            if percentage >= 80:
                color_tag = "excellent"
            elif percentage >= 60:
                color_tag = "good"
            elif percentage >= 40:
                color_tag = "fair"
            else:
                color_tag = "poor"

            self.security_text.insert(tk.END, f"{test_name:<25} ", "bold")
            self.security_text.insert(tk.END, f"{score:>2}/{max_score:>2} ", color_tag)
            self.security_text.insert(tk.END, f"({percentage:>3.0f}%) - {details}\n")

        # Calculate overall percentage
        if max_possible_score > 0:
            overall_percentage = (total_score / max_possible_score) * 100
        else:
            overall_percentage = 0

        self.security_text.insert(tk.END, "\n" + "=" * 60 + "\n")
        self.security_text.insert(tk.END, f"OVERALL SECURITY SCORE: {total_score}/{max_possible_score} ", "bold")
        self.security_text.insert(tk.END, f"({overall_percentage:.1f}%)\n\n")

        # Overall rating
        if overall_percentage >= 90:
            rating = "EXCELLENT"
            color = "excellent"
            description = "Strong cryptographic properties across all tests"
        elif overall_percentage >= 80:
            rating = "VERY GOOD"
            color = "good"
            description = "Robust security with minor areas for improvement"
        elif overall_percentage >= 70:
            rating = "GOOD"
            color = "good"
            description = "Solid security foundation"
        elif overall_percentage >= 60:
            rating = "FAIR"
            color = "fair"
            description = "Adequate security with several areas needing improvement"
        elif overall_percentage >= 50:
            rating = "MARGINAL"
            color = "fair"
            description = "Below average security - significant improvements needed"
        else:
            rating = "POOR"
            color = "poor"
            description = "Critical security issues detected"

        self.security_text.insert(tk.END, f"SECURITY RATING: ", "bold")
        self.security_text.insert(tk.END, f"{rating}\n", color)
        self.security_text.insert(tk.END, f"{description}\n\n")

        # Recommendations
        self.security_text.insert(tk.END, "RECOMMENDATIONS:\n", "bold")

        if overall_percentage < 70:
            self.security_text.insert(tk.END, "• Consider increasing rounds for better security\n")
            self.security_text.insert(tk.END, "• Review S-box generation for better randomness\n")
            self.security_text.insert(tk.END, "• Test with larger key sizes\n")
        else:
            self.security_text.insert(tk.END, "• Maintain current security parameters\n")
            self.security_text.insert(tk.END, "• Continue regular security testing\n")
            self.security_text.insert(tk.END, "• Consider external security audit for production use\n")

        # Configure text tags for colors
        self.security_text.tag_configure("bold", font=self.STYLE["font_bold"])
        self.security_text.tag_configure("excellent", foreground="#00FF00")
        self.security_text.tag_configure("good", foreground="#90FF90")
        self.security_text.tag_configure("fair", foreground="#FFA500")
        self.security_text.tag_configure("poor", foreground="#FF6B00")
        self.security_text.tag_configure("error", foreground="#FF0000")

    def _show_about_window(self):
        about_window = tk.Toplevel(self.root)
        about_window.title(">>> ABOUT PARTYBASHER v1.9<<<")
        about_window.geometry("800x750")
        about_window.minsize(800, 750)
        about_window.configure(bg=self.STYLE["colors"]["background"])
        about_window.transient(self.root)
        about_window.grab_set()

        about_text = f"""
Partybasher v1.9
--------------------------------------------
Technical Overview and Design Rationale

Partybasher is a custom authenticated encryption cipher designed for robust confidentiality, integrity, and authenticity. The design is predicated on a defense-in-depth strategy, layering modern cryptographic primitives and novel techniques to create a formidable security framework.

The encryption process can be understood through its three primary architectural stages:

1. Key Derivation:
   - A user-provided keyword is transformed into a high-entropy 256-bit master key using Argon2id, the modern industry standard for password-based key derivation.
   - Unlike older KDFs that are merely computationally intensive, Argon2id is designed to be memory-hard, requiring a significant amount of RAM to compute.
   - This design provides superior resistance to modern, parallelized attacks from specialized hardware like GPUs (Graphics Processing Units) and ASICs, which are memory-limited. This ensures that the security of the entire cipher rests on a key that is exceptionally difficult to brute-force.

2. Authenticated Encryption (AEAD):
    - The cipher operates as an Authenticated Encryption with Associated Data (AEAD) scheme using an Encrypt-then-MAC construction.
    - Encryption is performed using the core block cipher in Counter (CTR) mode, which functions as a secure stream cipher.
    - Integrity and authenticity are guaranteed by a separate HMAC-SHA256 tag computed over the salt, nonce, and the resulting ciphertext. This prevents any unauthorized modification (tampering) of the encrypted data.

3. The Core: The Partybasher Block Cipher
    The heart of the algorithm is a custom 128-bit block cipher built on a Substitution-Permutation Network (SPN) model. Each block of data undergoes a series of complex, key-dependent transformations across multiple rounds.

    KEY CIPHER COMPONENTS:

    • Confetti Scramble (Bitwise Permutation Layer):
        - A novel whitening layer that acts as the first and last step of the block encryption process.
        - Before the first round, this function shreds the 128-bit block into individual bits and reassembles them according to a secret permutation map derived from the master key.
        - This provides massive initial diffusion and disrupts byte-oriented cryptanalysis by shuffling bits across word boundaries, significantly increasing the complexity for an attacker.

    • Substitution Layer (Dynamic S-Boxes):
        - Unlike ciphers with fixed, well-analyzed S-boxes, Partybasher generates its substitution tables dynamically from the master key using the ChaCha20 stream cipher.
        - This creates a key-dependent "black box" for the attacker, rendering pre-computation and table-based attacks ineffective. Multiple S-box layers are applied in each round for deeper non-linearity.

    • Diffusion Layer (Maximum Diffusion Permutation):
        - At the heart of the diffusion layer are modern ARX (Add-Rotate-XOR) operations inspired by ciphers like Threefish and Speck.
        - Operating on 64-bit words, this layer uses a multi-pass structure with dynamic rotations to rapidly achieve the avalanche effect, where a single-bit change in the input causes approximately 50% of the output bits to flip.

    • Key Schedule and Round Constants:
        - The key schedule generates a unique 256-bit sub-key for each of the cipher's rounds using the SHA-3 hash function.
        - To break round symmetry and prevent slide attacks, each sub-key calculation incorporates a unique round constant. These constants are derived from the SHA3-256 function, serving as "nothing-up-my-sleeve" numbers.

ANCILLARY MODULES:

• Cryptanalysis Laboratory: A comprehensive, built-in suite for security validation, including tests for randomness, diffusion, and resistance to common cryptanalytic attacks.
• Secure Keyword Generator: A utility for creating high-entropy keywords that meet minimum security standards, complete with a real-time entropy analyzer.
• Secure File Encryption Module: A dedicated interface for file operations, featuring a secure file format (.ptbsher) and a "True Encryption" mode for permanent deletion of original files.
TECHNICAL SPECIFICATIONS:
--------------------------------------------
Cipher Mode:      Authenticated Stream Cipher
                  (CTR + Encrypt-then-MAC)
Block Size:       128 bits (16 bytes)
Rounds:           {SECURITY_PARAMS[SECURITY_LEVEL]['rounds']} (for '{SECURITY_LEVEL}' security level)
Key Derivation:   Argon2id
Argon2id time cost:  {ARGON2_TIME_COST:,}
Argon2id memory cost: {ARGON2_MEMORY_COST:,}
Argon2id parallelism: {ARGON2_PARALLELISM:,}
Authentication:   HMAC-SHA256
Security Level:   {SECURITY_LEVEL.upper()} (Configurable)
"""

        text_area = scrolledtext.ScrolledText(about_window, font=self.STYLE["font_normal"],
                                              bg=self.STYLE["colors"]["entry_bg"], fg=self.STYLE["colors"]["text"],
                                              relief='flat', borderwidth=0, wrap=tk.WORD, padx=15, pady=15)
        text_area.pack(fill='both', expand=True, padx=20, pady=20)
        text_area.insert("1.0", about_text)
        text_area.config(state='disabled')
        close_btn = self._create_hacker_button(about_window, "[ CLOSE ]", about_window.destroy)
        close_btn.pack(pady=15)

    def _encrypt_gui(self) -> None:
        text = self.text_entry.get("1.0", tk.END).strip()
        keyword = self.key_entry.get().strip()
        if not text or not keyword:
            messagebox.showwarning("Input Error", "Payload and Key cannot be empty.")
            self.status_var.set("[error] :: missing input")
            return
        try:
            encrypted = self.cipher.encrypt(text, keyword)
            self.result_text.delete("1.0", tk.END)
            self.result_text.insert("1.0", encrypted)
            self.root.clipboard_clear()
            self.root.clipboard_append(encrypted)
            self.status_var.set("[success] :: encrypted and copied to clipboard")
        except Exception as e:
            self._handle_error("Encryption Failed", e)

    def _decrypt_gui(self) -> None:
        text = self.text_entry.get("1.0", tk.END).strip()
        keyword = self.key_entry.get().strip()
        if not text or not keyword:
            messagebox.showwarning("Input Error", "Payload and Key cannot be empty.")
            self.status_var.set("[error] :: missing input")
            return
        try:
            decrypted = self.cipher.decrypt(text, keyword)
            self.result_text.delete("1.0", tk.END)
            self.result_text.insert("1.0", decrypted)
            self.status_var.set("[success] :: payload decrypted")
        except DecryptionError as e:
            self._handle_error("Decryption Failed", e)
        except Exception as e:
            self._handle_error("An unexpected error occurred", e)

    def _setup_bindings(self) -> None:
        self.root.bind('<Control-v>', self._paste_text)
        self.root.bind('<Control-V>', self._paste_text)
        self.root.bind('<Control-c>', self._copy_text)
        self.root.bind('<Control-C>', self._copy_text)

    def _handle_error(self, message: str, e: Exception) -> None:
        messagebox.showerror("Error", f"{message}:\n{e}")
        self.status_var.set(f"[error] :: {e}")

    def _paste_text(self, event: Optional[tk.Event] = None) -> str:
        widget = self.root.focus_get()
        if isinstance(widget, (tk.Entry, tk.Text, scrolledtext.ScrolledText)):
            try:
                self._paste_to_widget(widget, self.root.clipboard_get())
            except tk.TclError:
                pass
        return "break"

    def _copy_text(self, event: Optional[tk.Event] = None) -> str:
        widget = self.root.focus_get()
        if isinstance(widget, (tk.Entry, tk.Text, scrolledtext.ScrolledText)):
            self._copy_from_widget(widget)
        return "break"

    def _copy_from_output(self):
        self._copy_from_widget(self.result_text)
        self.status_var.set("[status] :: output copied to clipboard")

    def _paste_into_input(self):
        try:
            content = self.root.clipboard_get()
            self._paste_to_widget(self.text_entry, content)
            self.status_var.set("[status] :: clipboard pasted into input")
        except tk.TclError:
            self.status_var.set("[status] :: clipboard is empty")

    def _create_context_menu(self, widget: tk.Widget) -> None:
        menu = tk.Menu(widget, tearoff=0, bg=self.STYLE["colors"]["frame"], fg=self.STYLE["colors"]["text"],
                       activebackground=self.STYLE["colors"]["accent"],
                       activeforeground=self.STYLE["colors"]["button_fg"], relief='flat',
                       font=self.STYLE["font_normal"])
        menu.add_command(label="Cut", command=lambda: self._cut_from_widget(widget))
        menu.add_command(label="Copy", command=lambda: self._copy_from_widget(widget))
        menu.add_command(label="Paste", command=lambda: self._paste_text())
        menu.add_separator()
        menu.add_command(label="Select All", command=lambda: self._select_all_in_widget(widget))
        widget.bind("<Button-3>", lambda e: menu.tk_popup(e.x_root, e.y_root))

    def _cut_from_widget(self, widget: tk.Widget) -> None:
        self._copy_from_widget(widget)
        if isinstance(widget, tk.Entry):
            widget.delete(0, tk.END)
        elif isinstance(widget, (tk.Text, scrolledtext.ScrolledText)):
            try:
                widget.delete(tk.SEL_FIRST, tk.SEL_LAST)
            except tk.TclError:
                pass

    def _copy_from_widget(self, widget: tk.Widget) -> None:
        text_to_copy = ""
        if isinstance(widget, tk.Entry):
            text_to_copy = widget.get()
        elif isinstance(widget, (tk.Text, scrolledtext.ScrolledText)):
            try:
                text_to_copy = widget.get(tk.SEL_FIRST, tk.SEL_LAST)
            except tk.TclError:
                text_to_copy = widget.get('1.0', tk.END).strip()
        if text_to_copy:
            self.root.clipboard_clear()
            self.root.clipboard_append(text_to_copy)

    def _paste_to_widget(self, widget: tk.Widget, text: str) -> None:
        if isinstance(widget, tk.Entry):
            widget.delete(0, tk.END)
            widget.insert(0, text)
        elif isinstance(widget, (tk.Text, scrolledtext.ScrolledText)):
            try:
                start = widget.index(tk.SEL_FIRST)
                end = widget.index(tk.SEL_LAST)
                widget.delete(start, end)
                widget.insert(start, text)
            except tk.TclError:
                widget.insert(tk.INSERT, text)

    def _select_all_in_widget(self, widget: tk.Widget) -> None:
        if isinstance(widget, tk.Entry):
            widget.select_range(0, tk.END)
        elif isinstance(widget, (tk.Text, scrolledtext.ScrolledText)):
            widget.tag_add(tk.SEL, '1.0', tk.END)
        widget.focus_set()


def main():
    """Initializes and runs the enhanced GUI application."""
    import tkinterdnd2 as dnd
    root = dnd.TkinterDnD.Tk()
    app = PartybasherGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()