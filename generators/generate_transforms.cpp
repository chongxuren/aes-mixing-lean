// Deterministic integer inputs for Lean's finite mixed-moment certificates.
// The generated arithmetic is checked independently by Lean's kernel.
// Each invocation emits the fixed 255 pairs for one nonzero byte alpha.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>

using I = std::int64_t;

using Vec = std::array<I,256>;

using Bytes = std::array<unsigned,256>;

static constexpr I range_guard = I(1) << 54;

static const Bytes expected_inverse = {0,1,141,246,203,82,123,209,232,79,41,192,176,225,229,199,116,180,170,75,153,43,96,95,88,63,253,204,255,64,238,178,58,110,90,241,85,77,168,201,193,10,152,21,48,68,162,194,44,69,146,108,243,57,102,66,242,53,32,111,119,187,89,25,29,254,55,103,45,49,245,105,167,100,171,19,84,37,233,9,237,92,5,202,76,36,135,191,24,62,34,240,81,236,97,23,22,94,175,211,73,166,54,67,244,71,145,223,51,147,33,59,121,183,151,133,16,181,186,60,182,112,208,6,161,250,129,130,131,126,127,128,150,115,190,86,155,158,149,217,247,2,185,164,222,106,50,109,216,138,132,114,42,20,159,136,249,220,137,154,251,124,46,195,143,184,101,72,38,200,18,74,206,231,210,98,12,224,31,239,17,117,120,113,165,142,118,61,189,188,134,87,11,40,47,163,218,212,228,15,169,39,83,4,27,252,172,230,122,7,174,99,197,219,226,234,148,139,196,213,157,248,144,107,177,13,214,235,198,14,207,173,8,78,215,227,93,80,30,179,91,35,56,52,104,70,3,140,221,156,125,160,205,26,65,28};

static const Vec expected_walsh = {0,32,-16,-16,-16,-16,0,16,16,0,16,0,24,8,24,-8,-16,-16,8,8,0,16,-8,24,8,-24,-16,-16,0,16,8,8,12,-28,-4,-12,4,-4,-12,-4,-4,-12,-4,-12,-4,-12,28,4,20,12,-4,20,28,4,4,28,28,4,20,-4,-4,-12,-12,-4,16,0,-8,-8,16,0,-24,24,8,-24,16,0,-16,-16,8,8,24,8,24,-8,24,-8,-24,8,-24,24,-24,8,32,32,-16,-16,4,-4,28,4,-4,-12,4,28,-4,-12,20,-4,12,-28,-12,-20,20,12,20,-4,-4,4,12,20,-12,-4,20,12,4,-4,-12,-20,12,-28,-4,20,-12,-20,-12,-4,-12,-20,-12,-20,4,-4,-12,-4,-28,12,-20,-12,12,-28,-28,12,20,12,12,-28,-12,-4,-4,20,24,-8,-8,-8,-24,8,24,-24,16,0,0,16,24,-24,-8,-8,24,8,0,16,24,-8,16,0,-24,24,0,16,-16,-16,24,-24,12,20,4,28,-28,12,-4,4,12,20,4,-4,-4,4,-12,-4,-4,-12,28,4,20,-4,-12,-4,20,-4,-12,-20,20,12,-12,-20,32,32,24,-24,-16,-16,-24,8,16,0,-24,8,8,24,0,16,-24,24,-8,-8,-24,8,24,-8,0,16,-16,-16,-8,24,8,8};

static void require(bool b, const char* msg) {
  if (!b) throw std::runtime_error(msg);
}

static I checked(__int128 n) {
  if (n < -(__int128)range_guard || n > (__int128)range_guard)
    throw std::runtime_error("integer range guard exceeded");
  return I(n);
}

static I ipow(I a, int n) {
  I z=1; while(n--) z=checked((__int128)z*a); return z;
}

static unsigned mul(unsigned a, unsigned b) {
  unsigned z=0;
  for(int i=0;i<8;++i) {
    if(b&1) z^=a;
    a=((a<<1)^((a&128)?0x1b:0))&255; b>>=1;
  }
  return z;
}

static unsigned rot(unsigned x, unsigned n) { return ((x<<n)|(x>>(8-n)))&255; }
static unsigned affine(unsigned x) { return x^rot(x,1)^rot(x,2)^rot(x,3)^rot(x,4); }

static unsigned tr(unsigned x) { return ((x>>5)^(x>>7))&1; }

static void fwht(Vec& a) {
  for(unsigned len=1;len<256;len*=2)
    for(unsigned base=0;base<256;base+=2*len)
      for(unsigned j=0;j<len;++j) {
        I x=a[base+j], y=a[base+j+len];
        a[base+j]=checked((__int128)x+y);
        a[base+j+len]=checked((__int128)x-y);
      }
}

static unsigned ordinary_adjoint(unsigned value) {
  const unsigned basis[8]={30,110,60,152,203,223,23,156};
  unsigned out=0;
  for(unsigned j=0;j<8;++j)if(value&(1u<<j))out^=basis[j];
  return out;
}
int main(int argc,char**argv) {
  if(argc!=3)return 2;
  try {
    const std::string alpha_arg(argv[1]);
    require(!alpha_arg.empty() && alpha_arg.find_first_not_of("0123456789")==std::string::npos,
            "alpha must contain decimal digits only");
    std::size_t used=0;
    unsigned long parsed=std::stoul(argv[1], &used);
    require(used==std::string(argv[1]).size() && parsed>0 && parsed<256,"alpha must be an integer from 1 to 255");
    unsigned alpha=static_cast<unsigned>(parsed);
    std::ofstream out(argv[2]);require(bool(out),"output unavailable");
    std::array<std::array<Vec,5>,2> transforms{};Bytes trace{};
    for(unsigned k=0;k<256;++k)for(unsigned j=0;j<8;++j)trace[k]|=tr(mul(k,1u<<j))<<j;
    for(unsigned f=0;f<2;++f)for(unsigned r=1;r<=4;++r) {
      Vec& v=transforms[f][r];
      for(unsigned x=0;x<256;++x) {
        I p=f?ipow(expected_walsh[x]/4,2):(x==0?0:(tr(expected_inverse[x])?0:1)+(x==1?1:0));
        v[x]=ipow(p,r);
      }
      fwht(v);
    }
    for(unsigned beta=1;beta<256;++beta)for(unsigned f=0;f<2;++f)
      for(unsigned r=f?2:1;r<=(f?3:4);++r) {
        Vec v{};
        for(unsigned k=0;k<256;++k) {
          unsigned ak=mul(alpha,k);
          unsigned lt=mul(beta,f?affine(ak):ordinary_adjoint(ak));
          v[k]=checked((__int128)transforms[f][r][trace[lt]]*transforms[f][5-r][trace[k]]);
        }
        out<<"{\"alpha\":"<<alpha<<",\"beta\":"<<beta<<",\"family\":"<<f<<",\"power\":"<<r<<",\"stages\":[";
        for(unsigned s=0;s<9;++s) {
          out<<(s?",[":"[");
          for(unsigned i=0;i<256;++i)out<<(i?",":"")<<v[i];
          out<<"]";
          if(s<8) {
            Vec next{};
            for(unsigned i=0;i<256;++i)
              next[i]=(i&(1u<<s))?checked((__int128)v[i^(1u<<s)]-v[i]):checked((__int128)v[i]+v[i^(1u<<s)]);
            v=next;
          }
        }
        out<<"]}\n";
      }
    out.close();require(bool(out),"output write failed");return 0;
  } catch(const std::exception& e) {std::cerr<<e.what()<<'\n';return 1;}
}
