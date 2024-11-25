//***********************************************************************************
// 2018.04.01 created by Zexlus1126
//
//    Example 002
// This is a simple demonstration on calculating merkle root from merkle branch 
// and solving a block (#286819) which the information is downloaded from Block Explorer 
//***********************************************************************************

#include <iostream>
#include <fstream>
#include <string>
#include <chrono>

#include <cstdio>
#include <cstring>

#include <cassert>
#include <cuda_runtime.h>

// #include "sha256.h"

#define BLOCK_SIZE 128

#define _rotl(v, s) ((v)<<(s) | (v)>>(32-(s)))
#define _rotr(v, s) ((v)>>(s) | (v)<<(32-(s)))

#define _swap(x, y) (((x)^=(y)), ((y)^=(x)), ((x)^=(y)))

typedef unsigned int WORD;
typedef unsigned char BYTE;

typedef union _sha256_ctx{
	WORD h[8];
	BYTE b[32];
}SHA256;

////////////////////////   Block   /////////////////////

typedef struct _block
{
    unsigned int version;
    unsigned char prevhash[32];
    unsigned char merkle_root[32];
    unsigned int ntime;
    unsigned int nbits;
    unsigned int nonce;
}HashBlock;

typedef struct _sharedData
{
    HashBlock block;
    SHA256 sha256_ctx;
    SHA256 tmp;
}SharedData;

__constant__ static const WORD k[64] = {
	0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
	0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
	0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
	0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
	0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
	0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
	0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
	0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};
static const WORD h_k[64] = {
	0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
	0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
	0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
	0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
	0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
	0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
	0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
	0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

__device__ __forceinline__ void sha256_transform(SHA256 *ctx, const BYTE *msg)
{
	WORD a, b, c, d, e, f, g, h;
	WORD i, j;
	
	// Create a 64-entry message schedule array w[0..63] of 32-bit words
	WORD w[64];
	// Copy chunk into first 16 words w[0..15] of the message schedule array
	w[0]  = (msg[0]<<24)  | (msg[1]<<16)  | (msg[2]<<8)  | msg[3];
    w[1]  = (msg[4]<<24)  | (msg[5]<<16)  | (msg[6]<<8)  | msg[7];
    w[2]  = (msg[8]<<24)  | (msg[9]<<16)  | (msg[10]<<8) | msg[11];
    w[3]  = (msg[12]<<24) | (msg[13]<<16) | (msg[14]<<8) | msg[15];
    w[4]  = (msg[16]<<24) | (msg[17]<<16) | (msg[18]<<8) | msg[19];
    w[5]  = (msg[20]<<24) | (msg[21]<<16) | (msg[22]<<8) | msg[23];
    w[6]  = (msg[24]<<24) | (msg[25]<<16) | (msg[26]<<8) | msg[27];
    w[7]  = (msg[28]<<24) | (msg[29]<<16) | (msg[30]<<8) | msg[31];
    w[8]  = (msg[32]<<24) | (msg[33]<<16) | (msg[34]<<8) | msg[35];
    w[9]  = (msg[36]<<24) | (msg[37]<<16) | (msg[38]<<8) | msg[39];
    w[10] = (msg[40]<<24) | (msg[41]<<16) | (msg[42]<<8) | msg[43];
    w[11] = (msg[44]<<24) | (msg[45]<<16) | (msg[46]<<8) | msg[47];
    w[12] = (msg[48]<<24) | (msg[49]<<16) | (msg[50]<<8) | msg[51];
    w[13] = (msg[52]<<24) | (msg[53]<<16) | (msg[54]<<8) | msg[55];
    w[14] = (msg[56]<<24) | (msg[57]<<16) | (msg[58]<<8) | msg[59];
    w[15] = (msg[60]<<24) | (msg[61]<<16) | (msg[62]<<8) | msg[63];
	
	// Extend the first 16 words into the remaining 48 words w[16..63] of the message schedule array:
	for(i=16;i<64;++i)
	{
		WORD s0 = (_rotr(w[i-15], 7)) ^ (_rotr(w[i-15], 18)) ^ (w[i-15]>>3);
		WORD s1 = (_rotr(w[i-2], 17)) ^ (_rotr(w[i-2], 19))  ^ (w[i-2]>>10);
		w[i] = w[i-16] + s0 + w[i-7] + s1;
	}
	
	
	// Initialize working variables to current hash value
	a = ctx->h[0];
	b = ctx->h[1];
	c = ctx->h[2];
	d = ctx->h[3];
	e = ctx->h[4];
	f = ctx->h[5];
	g = ctx->h[6];
	h = ctx->h[7];
	
	// Compress function main loop:
	for(i=0;i<64;++i)
	{
		WORD S0 = (_rotr(a, 2)) ^ (_rotr(a, 13)) ^ (_rotr(a, 22));
		WORD S1 = (_rotr(e, 6)) ^ (_rotr(e, 11)) ^ (_rotr(e, 25));
		WORD ch = (e & f) ^ ((~e) & g);
		WORD maj = (a & b) ^ (a & c) ^ (b & c);
		WORD temp1 = h + S1 + ch + k[i] + w[i];
		WORD temp2 = S0 + maj;
		
		h = g;
		g = f;
		f = e;
		e = d + temp1;
		d = c;
		c = b;
		b = a;
		a = temp1 + temp2;
	}
	
	// Add the compressed chunk to the current hash value
	ctx->h[0] += a;
	ctx->h[1] += b;
	ctx->h[2] += c;
	ctx->h[3] += d;
	ctx->h[4] += e;
	ctx->h[5] += f;
	ctx->h[6] += g;
	ctx->h[7] += h;
	
}

__device__ void sha256(SHA256 *ctx, const BYTE *msg, size_t len)
{
	// Initialize hash values:
	// (first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19):
	ctx->h[0] = 0x6a09e667;
	ctx->h[1] = 0xbb67ae85;
	ctx->h[2] = 0x3c6ef372;
	ctx->h[3] = 0xa54ff53a;
	ctx->h[4] = 0x510e527f;
	ctx->h[5] = 0x9b05688c;
	ctx->h[6] = 0x1f83d9ab;
	ctx->h[7] = 0x5be0cd19;
	
	
	WORD i, j;
	size_t remain = len % 64;
	size_t total_len = len - remain;
	
	// Process the message in successive 512-bit chunks
	// For each chunk:
	for(i=0;i<total_len;i+=64)
	{
		sha256_transform(ctx, &msg[i]);
	}
	
	// Process remain data
	BYTE m[64] = {};
	for(i=total_len, j=0;i<len;++i, ++j)
	{
		m[j] = msg[i];
	}
	
	// Append a single '1' bit
	m[j++] = 0x80;  //1000 0000
	
	// Append K '0' bits, where k is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
	if(j > 56)
	{
		sha256_transform(ctx, m);
		memset(m, 0, sizeof(m));
		// printf("true\n");
	}
	
	// Append L as a 64-bit bug-endian integer, making the total post-processed length a multiple of 512 bits
	unsigned long long L = len * 8;  //bits
	m[63] = L;
	m[62] = L >> 8;
	m[61] = L >> 16;
	m[60] = L >> 24;
	m[59] = L >> 32;
	m[58] = L >> 40;
	m[57] = L >> 48;
	m[56] = L >> 56;
	sha256_transform(ctx, m);
	
	// Produce the final hash value (little-endian to big-endian)
	// Swap 1st & 4th, 2nd & 3rd byte for each word
	_swap(ctx->b[0], ctx->b[3]);
    _swap(ctx->b[1], ctx->b[2]);

    _swap(ctx->b[4], ctx->b[7]);
    _swap(ctx->b[5], ctx->b[6]);

    _swap(ctx->b[8], ctx->b[11]);
    _swap(ctx->b[9], ctx->b[10]);

    _swap(ctx->b[12], ctx->b[15]);
    _swap(ctx->b[13], ctx->b[14]);

    _swap(ctx->b[16], ctx->b[19]);
    _swap(ctx->b[17], ctx->b[18]);

    _swap(ctx->b[20], ctx->b[23]);
    _swap(ctx->b[21], ctx->b[22]);

    _swap(ctx->b[24], ctx->b[27]);
    _swap(ctx->b[25], ctx->b[26]);

    _swap(ctx->b[28], ctx->b[31]);
    _swap(ctx->b[29], ctx->b[30]);
}

// host version
void h_sha256_transform(SHA256 *ctx, const BYTE *msg)
{
	WORD a, b, c, d, e, f, g, h;
	WORD i, j;
	
	// Create a 64-entry message schedule array w[0..63] of 32-bit words
	WORD w[64];
	// Copy chunk into first 16 words w[0..15] of the message schedule array
	for(i=0, j=0;i<16;++i, j+=4)
	{
		w[i] = (msg[j]<<24) | (msg[j+1]<<16) | (msg[j+2]<<8) | (msg[j+3]);
	}
	
	// Extend the first 16 words into the remaining 48 words w[16..63] of the message schedule array:
	for(i=16;i<64;++i)
	{
		WORD s0 = (_rotr(w[i-15], 7)) ^ (_rotr(w[i-15], 18)) ^ (w[i-15]>>3);
		WORD s1 = (_rotr(w[i-2], 17)) ^ (_rotr(w[i-2], 19))  ^ (w[i-2]>>10);
		w[i] = w[i-16] + s0 + w[i-7] + s1;
	}
	
	
	// Initialize working variables to current hash value
	a = ctx->h[0];
	b = ctx->h[1];
	c = ctx->h[2];
	d = ctx->h[3];
	e = ctx->h[4];
	f = ctx->h[5];
	g = ctx->h[6];
	h = ctx->h[7];
	
	// Compress function main loop:
	for(i=0;i<64;++i)
	{
		WORD S0 = (_rotr(a, 2)) ^ (_rotr(a, 13)) ^ (_rotr(a, 22));
		WORD S1 = (_rotr(e, 6)) ^ (_rotr(e, 11)) ^ (_rotr(e, 25));
		WORD ch = (e & f) ^ ((~e) & g);
		WORD maj = (a & b) ^ (a & c) ^ (b & c);
		WORD temp1 = h + S1 + ch + h_k[i] + w[i];
		WORD temp2 = S0 + maj;
		
		h = g;
		g = f;
		f = e;
		e = d + temp1;
		d = c;
		c = b;
		b = a;
		a = temp1 + temp2;
	}
	
	// Add the compressed chunk to the current hash value
	ctx->h[0] += a;
	ctx->h[1] += b;
	ctx->h[2] += c;
	ctx->h[3] += d;
	ctx->h[4] += e;
	ctx->h[5] += f;
	ctx->h[6] += g;
	ctx->h[7] += h;
	
}

void h_sha256(SHA256 *ctx, const BYTE *msg, size_t len)
{
	// Initialize hash values:
	// (first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19):
	ctx->h[0] = 0x6a09e667;
	ctx->h[1] = 0xbb67ae85;
	ctx->h[2] = 0x3c6ef372;
	ctx->h[3] = 0xa54ff53a;
	ctx->h[4] = 0x510e527f;
	ctx->h[5] = 0x9b05688c;
	ctx->h[6] = 0x1f83d9ab;
	ctx->h[7] = 0x5be0cd19;
	
	
	WORD i, j;
	size_t remain = len % 64;
	size_t total_len = len - remain;
	
	// Process the message in successive 512-bit chunks
	// For each chunk:
	for(i=0;i<total_len;i+=64)
	{
		h_sha256_transform(ctx, &msg[i]);
	}
	
	// Process remain data
	BYTE m[64] = {};
	for(i=total_len, j=0;i<len;++i, ++j)
	{
		m[j] = msg[i];
	}
	
	// Append a single '1' bit
	m[j++] = 0x80;  //1000 0000
	
	// Append K '0' bits, where k is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
	if(j > 56)
	{
		h_sha256_transform(ctx, m);
		memset(m, 0, sizeof(m));
		printf("true\n");
	}
	
	// Append L as a 64-bit bug-endian integer, making the total post-processed length a multiple of 512 bits
	unsigned long long L = len * 8;  //bits
	m[63] = L;
	m[62] = L >> 8;
	m[61] = L >> 16;
	m[60] = L >> 24;
	m[59] = L >> 32;
	m[58] = L >> 40;
	m[57] = L >> 48;
	m[56] = L >> 56;
	h_sha256_transform(ctx, m);
	
	// Produce the final hash value (little-endian to big-endian)
	// Swap 1st & 4th, 2nd & 3rd byte for each word
	for(i=0;i<32;i+=4)
	{
        _swap(ctx->b[i], ctx->b[i+3]);
        _swap(ctx->b[i+1], ctx->b[i+2]);
	}
}

////////////////////////   Utils   ///////////////////////

//convert one hex-codec char to binary
unsigned char decode(unsigned char c)
{
    switch(c)
    {
        case 'a':
            return 0x0a;
        case 'b':
            return 0x0b;
        case 'c':
            return 0x0c;
        case 'd':
            return 0x0d;
        case 'e':
            return 0x0e;
        case 'f':
            return 0x0f;
        case '0' ... '9':
            return c-'0';
    }
}


// convert hex string to binary
//
// in: input string
// string_len: the length of the input string
//      '\0' is not included in string_len!!!
// out: output bytes array
void convert_string_to_little_endian_bytes(unsigned char* out, char *in, size_t string_len)
{
    assert(string_len % 2 == 0);

    size_t s = 0;
    size_t b = string_len/2-1;

    for(s, b; s < string_len; s+=2, --b)
    {
        out[b] = (unsigned char)(decode(in[s])<<4) + decode(in[s+1]);
    }
}

// print out binary array (from highest value) in the hex format
void print_hex(unsigned char* hex, size_t len)
{
    for(int i=0;i<len;++i)
    {
        printf("%02x", hex[i]);
    }
    printf("\n");
}


// print out binar array (from lowest value) in the hex format
void print_hex_inverse(unsigned char* hex, size_t len)
{
    for(int i=len-1;i>=0;--i)
    {
        printf("%02x", hex[i]);
    }
    printf("\n");
}

// __device__ int little_endian_bit_comparison(const unsigned char *a, const unsigned char *b)
// {
//     const unsigned int *a_int = reinterpret_cast<const unsigned int*>(a);
//     const unsigned int *b_int = reinterpret_cast<const unsigned int*>(b);
//     // compared from lowest bit
//     int result = 0;
//     result = (result << 1) + (a_int[7] > b_int[7]) - (a_int[7] < b_int[7]);
//     result = (result << 1) + (a_int[6] > b_int[6]) - (a_int[6] < b_int[6]);
//     result = (result << 1) + (a_int[5] > b_int[5]) - (a_int[5] < b_int[5]);
//     result = (result << 1) + (a_int[4] > b_int[4]) - (a_int[4] < b_int[4]);
//     result = (result << 1) + (a_int[3] > b_int[3]) - (a_int[3] < b_int[3]);
//     result = (result << 1) + (a_int[2] > b_int[2]) - (a_int[2] < b_int[2]);
//     result = (result << 1) + (a_int[1] > b_int[1]) - (a_int[1] < b_int[1]);
//     result = (result << 1) + (a_int[0] > b_int[0]) - (a_int[0] < b_int[0]);
//     return result;
// }

void getline(char *str, size_t len, FILE *fp)
{

    int i=0;
    while( i<len && (str[i] = fgetc(fp)) != EOF && str[i++] != '\n');
    str[len-1] = '\0';
}

////////////////////////   Hash   ///////////////////////

__device__ void double_sha256(SharedData *data)
{
    sha256(&data->tmp, (BYTE*)&data->block, sizeof(HashBlock));
    sha256(&data->sha256_ctx, (BYTE*)&data->tmp, sizeof(SHA256));
}
void h_double_sha256(SHA256 *sha256_ctx, unsigned char *bytes, size_t len)
{
    SHA256 tmp;
    h_sha256(&tmp, (BYTE*)bytes, len);
    h_sha256(sha256_ctx, (BYTE*)&tmp, sizeof(tmp));
}

////////////////////   Find Nonce   /////////////////////


__global__ void find_nonce(__restrict__ HashBlock *block, unsigned char* __restrict__ target, unsigned int *solution) {
    __shared__ SharedData d_data[BLOCK_SIZE];

    d_data[threadIdx.x].block = *block;

    unsigned int nonce = blockIdx.x * blockDim.x + threadIdx.x;
    unsigned int stride = gridDim.x * blockDim.x;

    for (; 0xffffffff - nonce >= stride && !solution[0]; nonce += stride) {
        d_data[threadIdx.x].block.nonce = nonce;

        // Compute double SHA-256
        double_sha256(&d_data[threadIdx.x]);

        // Check if the hash is less than the target
        const unsigned int *a_int = reinterpret_cast<const unsigned int*>(d_data[threadIdx.x].sha256_ctx.b);
        const unsigned int *b_int = reinterpret_cast<const unsigned int*>(target);
        // compared from lowest bit
        int result = 0;
        result = (result << 1) + (a_int[7] > b_int[7]) - (a_int[7] < b_int[7]);
        result = (result << 1) + (a_int[6] > b_int[6]) - (a_int[6] < b_int[6]);
        result = (result << 1) + (a_int[5] > b_int[5]) - (a_int[5] < b_int[5]);
        result = (result << 1) + (a_int[4] > b_int[4]) - (a_int[4] < b_int[4]);
        result = (result << 1) + (a_int[3] > b_int[3]) - (a_int[3] < b_int[3]);
        result = (result << 1) + (a_int[2] > b_int[2]) - (a_int[2] < b_int[2]);
        result = (result << 1) + (a_int[1] > b_int[1]) - (a_int[1] < b_int[1]);
        result = (result << 1) + (a_int[0] > b_int[0]) - (a_int[0] < b_int[0]);

        // Write the solution and signal that a valid nonce is found
        solution[(result >= 0)] = nonce;
    }
}

////////////////////   Merkle Root   /////////////////////


// calculate merkle root from several merkle branches
// root: output hash will store here (little-endian)
// branch: merkle branch  (big-endian)
// count: total number of merkle branch
void calc_merkle_root(unsigned char *root, int count, char **branch)
{
    size_t total_count = count; // merkle branch
    unsigned char *raw_list = new unsigned char[(total_count+1)*32];
    unsigned char **list = new unsigned char*[total_count+1];

    // copy each branch to the list
    for(int i=0;i<total_count; ++i)
    {
        list[i] = raw_list + i * 32;
        //convert hex string to bytes array and store them into the list
        convert_string_to_little_endian_bytes(list[i], branch[i], 64);
    }

    list[total_count] = raw_list + total_count*32;


    // calculate merkle root
    while(total_count > 1)
    {
        
        // hash each pair
        int i, j;

        if(total_count % 2 == 1)  //odd, 
        {
            memcpy(list[total_count], list[total_count-1], 32);
        }

        for(i=0, j=0;i<total_count;i+=2, ++j)
        {
            // this part is slightly tricky,
            //   because of the implementation of the double_sha256,
            //   we can avoid the memory begin overwritten during our sha256d calculation
            // double_sha:
            //     tmp = hash(list[0]+list[1])
            //     list[0] = hash(tmp)
            h_double_sha256((SHA256*)list[j], list[i], 64);
        }

        total_count = j;
    }

    memcpy(root, list[0], 32);

    delete[] raw_list;
    delete[] list;
}


void solve(FILE *fin, FILE *fout)
{

    // **** read data *****
    char version[9];
    char prevhash[65];
    char ntime[9];
    char nbits[9];
    int tx;
    char *raw_merkle_branch;
    char **merkle_branch;

    getline(version, 9, fin);
    getline(prevhash, 65, fin);
    getline(ntime, 9, fin);
    getline(nbits, 9, fin);
    fscanf(fin, "%d\n", &tx);
    printf("start hashing");

    raw_merkle_branch = new char [tx * 65];
    merkle_branch = new char *[tx];
    for(int i=0;i<tx;++i)
    {
        merkle_branch[i] = raw_merkle_branch + i * 65;
        getline(merkle_branch[i], 65, fin);
        merkle_branch[i][64] = '\0';
    }

    // **** calculate merkle root ****

    unsigned char merkle_root[32];
    calc_merkle_root(merkle_root, tx, merkle_branch);

    // fprintf(stderr, "merkle root(little): ");
    // print_hex(merkle_root, 32);
    // fprintf(stderr, "\n");

    // fprintf(stderr, "merkle root(big):    ");
    // print_hex_inverse(merkle_root, 32);
    // fprintf(stderr, "\n");

    // **** solve block ****
    // fprintf(stderr, "Block info (big): \n");
    // fprintf(stderr, "  version:  %s\n", version);
    // fprintf(stderr, "  pervhash: %s\n", prevhash);
    // fprintf(stderr, "  merkleroot: "); print_hex_inverse(merkle_root, 32); fprintf(stderr, "\n");
    // fprintf(stderr, "  nbits:    %s\n", nbits);
    // fprintf(stderr, "  ntime:    %s\n", ntime);
    // fprintf(stderr, "  nonce:    ???\n\n");

    HashBlock block;

    // convert to byte array in little-endian
    convert_string_to_little_endian_bytes((unsigned char *)&block.version, version, 8);
    convert_string_to_little_endian_bytes(block.prevhash,                  prevhash,    64);
    memcpy(block.merkle_root, merkle_root, 32);
    convert_string_to_little_endian_bytes((unsigned char *)&block.nbits,   nbits,     8);
    convert_string_to_little_endian_bytes((unsigned char *)&block.ntime,   ntime,     8);
    block.nonce = 0;
    
    
    // ********** calculate target value *********
    // calculate target value from encoded difficulty which is encoded on "nbits"
    unsigned int exp = block.nbits >> 24;
    unsigned int mant = block.nbits & 0xffffff;
    unsigned char target_hex[32] = {};
    
    unsigned int shift = 8 * (exp - 3);
    unsigned int sb = shift / 8;
    unsigned int rb = shift % 8;
    
    // little-endian
    target_hex[sb    ] = (mant << rb);
    target_hex[sb + 1] = (mant >> (8-rb));
    target_hex[sb + 2] = (mant >> (16-rb));
    target_hex[sb + 3] = (mant >> (24-rb));
    
    
    // printf("Target value (big): ");
    // print_hex_inverse(target_hex, 32);
    // printf("\n");
    // fflush(stdout);


    // fprintf(stderr, "start to find nonce\n");
    // ********** find nonce **************
    HashBlock *d_block;
    unsigned char *d_target;
    unsigned int *d_solution;
    unsigned int h_solution[2] = {};
    unsigned char h_found_flag = 0;
    unsigned char *d_found_flag;
    
    cudaError_t err;
    
    // Allocate memory on the device
    cudaMalloc(&d_block, sizeof(HashBlock));
    cudaMalloc(&d_target, 32 * sizeof(unsigned char));
    cudaMalloc(&d_solution, sizeof(unsigned int));
    // cudaMalloc(&d_found_flag, sizeof(unsigned char));

    err = cudaGetLastError();
    if (err != cudaSuccess){
        fprintf(stderr, "cudaMalloc error: %s\n", cudaGetErrorString(err));
    }

    // Copy data to the device
    // cudaMemcpy(d_found_flag, &h_found_flag, sizeof(unsigned char), cudaMemcpyHostToDevice);
    cudaMemcpy(d_solution, h_solution, 2 * sizeof(unsigned char), cudaMemcpyHostToDevice);
    cudaMemcpy(d_block, &block, sizeof(HashBlock), cudaMemcpyHostToDevice);
    cudaMemcpy(d_target, target_hex, 32 * sizeof(unsigned char), cudaMemcpyHostToDevice);

    err = cudaGetLastError();
    if (err != cudaSuccess){
        fprintf(stderr, "cudaMemcpy error: %s\n", cudaGetErrorString(err));
    }

    // Set the cache configuration for the kernel
    cudaFuncSetCacheConfig(find_nonce, cudaFuncCachePreferShared);

    auto start_kernel = std::chrono::high_resolution_clock::now();
    // Launch kernel
    int threads_per_block = 128;
    int blocks_per_grid = 2560; // Adjust based on your GPU
    find_nonce<<<blocks_per_grid, threads_per_block>>>(d_block, d_target, d_solution);

    err = cudaGetLastError();
    if (err != cudaSuccess){
        fprintf(stderr, "find_nonce error: %s\n", cudaGetErrorString(err));
    }

    cudaDeviceSynchronize();

    err = cudaGetLastError();
    if (err != cudaSuccess){
        fprintf(stderr, "DeviceSynchronize error: %s\n", cudaGetErrorString(err));
    }
    auto end_kernel = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> kernel_time = end_kernel - start_kernel;
    std::cout << " Kernel Time: " << kernel_time.count() << " s" << std::endl;

    // Copy the result back to the host
    cudaMemcpy(&h_solution, d_solution, sizeof(unsigned int), cudaMemcpyDeviceToHost);

    err = cudaGetLastError();
    if (err != cudaSuccess){
        fprintf(stderr, "cudaMemcpy error: %s\n", cudaGetErrorString(err));
    }
    
    // SHA256 sha256_ctx;
    
    // for(block.nonce=0x00000000; block.nonce<=0xf;++block.nonce)
    // {   
    //     //sha256d
    //     h_double_sha256(&sha256_ctx, (unsigned char*)&block, sizeof(block));
    //     print_hex(sha256_ctx.b, 32);
        
    //     if(little_endian_bit_comparison(sha256_ctx.b, target_hex, 32) < 0)  // sha256_ctx < target_hex
    //     {
    //         printf("Found Solution!!\n");
    //         printf("hash #%10u (big): ", block.nonce);
    //         print_hex_inverse(sha256_ctx.b, 32);
    //         printf("\n\n");

    //         break;
    //     }
    // }
    

    // print result

    //little-endian
    // printf("hash(little): ");
    // print_hex(sha256_ctx.b, 32);
    // printf("\n");

    // //big-endian
    // printf("hash(big):    ");
    // print_hex_inverse(sha256_ctx.b, 32);
    // printf("\n\n");

    fprintf(stderr, "nonce: %u\n", h_solution[0]);

    for(int i=0;i<4;++i)
    {
        fprintf(fout, "%02x", ((unsigned char*)&h_solution)[i]);
    }
    fprintf(fout, "\n");

    // for(int i=0;i<4;++i)
    // {
    //     fprintf(fout, "%02x", ((unsigned char*)&block.nonce)[i]);
    // }
    // fprintf(fout, "\n");
    

    delete[] merkle_branch;
    delete[] raw_merkle_branch;
}

int main(int argc, char **argv)
{
    if (argc != 3) {
        fprintf(stderr, "usage: cuda_miner <in> <out>\n");
    }
    FILE *fin = fopen(argv[1], "r");
    FILE *fout = fopen(argv[2], "w");

    int totalblock;

    fscanf(fin, "%d\n", &totalblock);
    fprintf(fout, "%d\n", totalblock);

    for(int i=0;i<totalblock;++i)
    {
        solve(fin, fout);
    }

    return 0;
}

