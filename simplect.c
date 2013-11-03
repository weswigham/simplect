/*
Simplect - A complexion of simplex noise and curve interpolation to create a block cipher

Variations:
Simplect64 - A lightweight version for testing, operates with 64 bit keys.
Simplect256 - The standard 32 bit implementation, operates on 256 bit keys.
Simplect512 - A 64 bit implementation for increased security in native 64 bit systems, 512 bit keys.
*/

#include <stdint.h>

#define VSIZE uint8_t /* Base type. 8-bit type for Simplect64, 32 for 256, and 64 for 512 */
#define KEYSIZE (sizeof(VSIZE)*8) /* Bytes per key */
#define BLOCKSIZE (KEYSIZE) /* Bytes per block */

VSIZE MAXIMUM_VAL = -1;

VSIZE wrapping_bezier(VSIZE p1, VSIZE p2, VSIZE p3, VSIZE p4, VSIZE t) {
    VSIZE mt = (MAXIMUM_VAL-t);
    VSIZE c1 = mt*mt*mt;
    VSIZE c2 = mt*mt*t*3;
    VSIZE c3 = mt*t*t*3;
    VSIZE c4 = t*t*t;
    return c1*p1+c2*p2+c3*p3+c4*p4;
}

#define MIDVAL MAXIMUM_VAL/2

VSIZE gradients3d[12][3];

int pg3d[12][3] = {{1,1,0},{-1,1,0},{1,-1,0},{-1,-1,0},
{1,0,1},{-1,0,1},{1,0,-1},{-1,0,-1},
{0,1,1},{0,-1,1},{0,1,-1},{0,-1,-1}};
                        
int p[256] = {151,160,137,91,90,15,
131,13,201,95,96,53,194,233,7,225,140,36,103,30,69,142,8,99,37,240,21,10,23,
190, 6,148,247,120,234,75,0,26,197,62,94,252,219,203,117,35,11,32,57,177,33,
88,237,149,56,87,174,20,125,136,171,168, 68,175,74,165,71,134,139,48,27,166,
77,146,158,231,83,111,229,122,60,211,133,230,220,105,92,41,55,46,245,40,244,
102,143,54, 65,25,63,161, 1,216,80,73,209,76,132,187,208, 89,18,169,200,196,
135,130,116,188,159,86,164,100,109,198,173,186, 3,64,52,217,226,250,124,123,
5,202,38,147,118,126,255,82,85,212,207,206,59,227,47,16,58,17,182,189,28,42,
223,183,170,213,119,248,152, 2,44,154,163, 70,221,153,101,155,167, 43,172,9,
129,22,39,253, 19,98,108,110,79,113,224,232,178,185, 112,104,218,246,97,228,
251,34,242,193,238,210,144,12,191,179,162,241, 81,51,145,235,249,14,239,107,
49,192,214, 31,181,199,106,157,184, 84,204,176,115,121,50,45,127, 4,150,254,
138,236,205,93,222,114,67,29,24,72,243,141,128,195,78,66,215,61,156,180};

int perm[512];

static void con() __attribute__((constructor));

/*
From what I can tell, we can always find an irreducible 
polynomial in the form 
0b101010101010...1011
(Every other bit is 1 add 1).
And so we'll use this as the polynomial for our finite field.
*/
VSIZE poly = 0;

void con() {
    int i = 0;
    for (i = 0 ; i < 255 ; i++) {
        perm[i] = p[i];
        perm[i+256] = p[i];
    }
    
    int j, k;
    for (j=0; j<12; j++) {
        for (k=0; k<3; k++) {
            if (pg3d[j][k]==0) {
                gradients3d[j][k] = 0;
            } else if (pg3d[j][k]==1) {
                gradients3d[j][k] = MAXIMUM_VAL;
            } else {
                gradients3d[j][k] = MAXIMUM_VAL >> 1;
            }
        }
    }
    
    for (i=1;i<(sizeof(VSIZE)*8);i+=2) {
        poly |= (1<<i);
    }
    poly |= 1;
}

//Adapted from the wikipedia Rijndael finite field article
VSIZE fmul(VSIZE a, VSIZE b) {
    VSIZE product = 0;
    VSIZE count = 0;
    VSIZE carry = 0;
    for (count = 0; count < (sizeof(VSIZE) << 3); count++) {
        if (b & 1)
            product ^= a;
        carry = a & (1<<(sizeof(VSIZE) << 3 - 1));
        a <<= 1;
        if (carry)
            a ^= poly;
        b >>= 1;
    }
    return product;
}

VSIZE Dot3D(VSIZE tbl[], VSIZE x, VSIZE y, VSIZE z)
{
    return fmul(tbl[0],x) ^ fmul(tbl[1],y) ^ fmul(tbl[2],z);
}

VSIZE Noise3D(VSIZE xin, VSIZE yin, VSIZE zin)
{
    VSIZE n0, n1, n2, n3;
    
    VSIZE F3 = MAXIMUM_VAL >> 1;
    VSIZE s = fmul(xin^yin^zin, F3);
    VSIZE i = xin^s;
    VSIZE j = yin^s;
    VSIZE k = zin^s;
    
    VSIZE G3 = MAXIMUM_VAL >> 2; 
    VSIZE t = fmul(i^j^k, G3);
    
    VSIZE X0 = i^t; 
    VSIZE Y0 = j^t;
    VSIZE Z0 = k^t;
    
    VSIZE x0 = xin^X0;
    VSIZE y0 = yin^Y0;
    VSIZE z0 = zin^Z0;
    
    VSIZE i1, j1, k1; 
    VSIZE i2, j2, k2; 
    
    if (x0>=y0){
        if (y0>=z0){
            i1=MAXIMUM_VAL; j1=0; k1=0; i2=MAXIMUM_VAL; j2=MAXIMUM_VAL; k2=0; // X Y Z order
        }
        else if (x0>=z0){
            i1=MAXIMUM_VAL; j1=0; k1=0; i2=MAXIMUM_VAL; j2=0; k2=MAXIMUM_VAL; // X Z Y order
        }
        else{
            i1=0; j1=0; k1=MAXIMUM_VAL; i2=MAXIMUM_VAL; j2=0; k2=MAXIMUM_VAL;  // Z X Y order
        }
    }
    else{ // x0<y0
        if (y0<z0){
            i1=0; j1=0; k1=MAXIMUM_VAL; i2=0; j2=MAXIMUM_VAL; k2=MAXIMUM_VAL; // Z Y X order
        }
        else if (x0<z0){
            i1=0; j1=MAXIMUM_VAL; k1=0; i2=0; j2=MAXIMUM_VAL; k2=MAXIMUM_VAL; // Y Z X order
        }
        else{ 
            i1=0; j1=MAXIMUM_VAL; k1=0; i2=MAXIMUM_VAL; j2=MAXIMUM_VAL; k2=0; // Y X Z order
        }
    }
    
    
    VSIZE x1 = x0 ^ i1 ^ G3; 
    VSIZE y1 = y0 ^ j1 ^ G3;
    VSIZE z1 = z0 ^ k1 ^ G3;
    
    VSIZE x2 = x0 ^ i2 ^ (G3 << 1);
    VSIZE y2 = y0 ^ j2 ^ (G3 << 1);
    VSIZE z2 = z0 ^ k2 ^ (G3 << 1);
    
    VSIZE x3 = x0 ^ MAXIMUM_VAL ^ (G3 << 1) ^ G3; 
    VSIZE y3 = y0 ^ MAXIMUM_VAL ^ (G3 << 1) ^ G3;
    VSIZE z3 = z0 ^ MAXIMUM_VAL ^ (G3 << 1) ^ G3;
    
    VSIZE ii = i & 255;
    VSIZE jj = j & 255;
    VSIZE kk = k & 255;
    
    
    VSIZE gi0 = perm[(ii^perm[(jj^perm[kk]) % 256]) %256] % 12;
    VSIZE gi1 = perm[(ii^i1^perm[(jj^j1^perm[(kk^k1) % 256]) % 256]) % 256] % 12;
    VSIZE gi2 = perm[(ii^i2^perm[(jj^j2^perm[(kk^k2) % 256]) % 256]) % 256] % 12;
    VSIZE gi3 = perm[(ii^1^perm[(jj^1^perm[(kk^1) % 256]) % 256]) % 256] % 12;
    
    VSIZE t0 = (MIDVAL) ^ fmul(x0,x0) ^ fmul(y0,y0) ^ fmul(z0,z0);
    
    t0 = fmul(t0,t0);
    n0 = fmul( fmul(t0, t0), Dot3D(gradients3d[gi0], x0, y0, z0));
    
    VSIZE t1 = (MIDVAL) ^ fmul(x1,x1) ^ fmul(y1,y1) ^ fmul(z1,z1);
    
    t1 = fmul(t1,t1);
    n1 = fmul(fmul(t1, t1), Dot3D(gradients3d[gi1], x1, y1, z1));
    
    VSIZE t2 = (MIDVAL) ^ fmul(x2,x2) ^ fmul(y2,y2) ^ fmul(z2,z2);
    
    t2 = fmul(t2,t2);
    n2 = fmul(fmul(t2,t2), Dot3D(gradients3d[gi2], x2, y2, z2));
    
    VSIZE t3 = (MIDVAL) ^ fmul(x3,x3) ^ fmul(y3,y3) ^ fmul(z3,z3);
    
    t3 = fmul(t3,t3);
    n3 = fmul(fmul(t3,t3), Dot3D(gradients3d[gi3], x3, y3, z3));
    
    VSIZE retval = (n0 ^ n1 ^ n2 ^ n3);
    
    return retval;
}

#define RLEFT(v, n) ((v << n) | (v >> ((sizeof(VSIZE)<<3) - n)))

void encode_block(uint8_t * key, uint8_t * block) {
    VSIZE * key_blocks = (VSIZE *)(void *)key;
    
    long int c = 0;
    for (c=0; c<BLOCKSIZE; c++) {
        int d = 0;
        for (d=0; d<8; d++) {
            //Bezier to find x coordinates
            
            VSIZE frac = (MAXIMUM_VAL/(BLOCKSIZE*8));
            
            VSIZE x = wrapping_bezier( key_blocks[0],
                            key_blocks[2],
                            key_blocks[4],
                            key_blocks[6],
                            frac*c + ((d+1)/(8)*frac) );
            //Bezier to find y coordinates
            VSIZE y = wrapping_bezier( key_blocks[1],
                            key_blocks[3],
                            key_blocks[5],
                            key_blocks[7],
                            frac*c + ((d+1)/(8)*frac) );
            VSIZE value = Noise3D(x, y, d^c); //Find the noise value
            if (value>(MIDVAL)) {
                block[c] ^= (1<<d);
            }
        }
        block[c] ^= RLEFT(key[c], c);
        key[(c+1) % KEYSIZE] ^= block[c];
    }
}

uint64_t tests[] = {
    0,
    0xFFFFFFFFFFFFFFFF,
    0xF0F0F0F0F0F0F0F0,
    0x0F0F0F0F0F0F0F0F,
    0xEEEEEEEEEEEEEEEE,
    0x1111111111111111,
    0x0123456789ABCDEF,
    0xFEDCBA9876543210,
    0x1234567876543210,
    0x8765432101234567,
    0x1,
    0x2,
};
#define NUM_TESTS (12)

#include <stdio.h>

int main() {
    
    uint32_t i = 0;
    for (i=0;i<NUM_TESTS;i++) {
    
        printf("Using key %016lX, encoding the zero-string!\n", tests[i]);
    
        uint64_t key = tests[i];
        uint8_t * key_ptr = (uint8_t *)(void *)&key;
        
        uint64_t block = 0;
        uint8_t * block_ptr = (uint8_t *)(void *)&block;
        
        encode_block(key_ptr, block_ptr);
        
        printf("Block result: %016lX\n" ,block);
        
        encode_block(key_ptr, block_ptr);
        
        printf("Reversing it: %016lX\n" ,block);
    
    }
    
    uint64_t key = 0;
    uint8_t * key_ptr = (uint8_t *)(void *)&key;
    
    uint64_t block = 0;
    uint8_t * block_ptr = (uint8_t *)(void *)&block;
    
    uint64_t total = 0;
    
    for (i=0;i<64;i++) {
        key ^= 1<<i;
        
        uint64_t res = block;
        uint8_t * res_ptr = (uint8_t *)(void *)&res;
        
        encode_block(key_ptr, res_ptr);
        
        uint64_t diff = block ^ res;
        
        uint64_t j = 0;
        uint64_t count = 0;
        for (j=0;j<64;j++) {
            if (diff&(1<<j))
                count++;
        }
        
        printf("%016lX -> %016lX differs in %ld bits\n", block, res, count);
    
        total += count;
    }

    printf("%ld bits differ on average.\n", total/64);
    
    return 0;
}