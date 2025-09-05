#include<vector>
#include<iostream>
#include<iomanip>
#include<algorithm>
#include<cmath>
namespace __FFT{
    constexpr double PI2=6.283185307179586231995927;
    struct complex{
        double real,imag;
        inline complex operator+(const complex &x)const{
            return {real+x.real,imag+x.imag};
        }
        inline complex operator-(const complex &x)const{
            return {real-x.real,imag-x.imag};
        }
        inline complex operator*(const complex &x)const{
            return {real*x.real-imag*x.imag,real*x.imag+x.real*imag};
        }
    };
    std::vector<complex> omega;
    inline void init_omega(const int &n){
        if(n<int(omega.size())) return;
        int start=omega.empty()?1:omega.size()<<1;
        omega.resize(1<<std::__lg(n));
        for(int i=start;i<=n;i<<=1)
            for(int j=0;j<(i>>1);j++){
                double arg=PI2*j/i;
                omega[(i>>1)+j]={cos(arg),sin(arg)};
            }
    }
    inline void FFT(std::vector<complex> &a,int n,bool inv){
        for(int i=0,j=0;i<n;i++){
            if(i<j) std::swap(a[i],a[j]);
            for(int l=n>>1;(j^=l)<l;l>>=1);
        }
        for(int len=2;len<=n;len<<=1)
            for(int i=0;i<n;i+=len)
                for(int j=0;j<(len>>1);j++){
                    complex w=inv?complex({omega[(len>>1)+j].real,-omega[(len>>1)+j].imag}):omega[(len>>1)+j];
                    complex x=a[i+j],y=a[i+j+(len>>1)]*w;
                    a[i+j]=x+y,a[i+j+(len>>1)]=x-y;
                }
        if(inv) for(int i=0;i<n;i++) a[i].real/=n;
    }
}
constexpr int BASE=10000;
constexpr int DIGITS_PER_BASE=4;
class bigint{
private:
    std::vector<int> num;
    bool is_negative;
    static int cmp_abs(const bigint &a,const bigint &b){
        if(a.num.size()!=b.num.size())
            return a.num.size()<b.num.size()?-1:1;
        for(int i=int(a.num.size())-1;i>=0;i--)
            if(a.num[i]!=b.num[i])
                return a.num[i]<b.num[i]?-1:1;
        return 0;
    }
public:
    bigint():is_negative(false){num.push_back(0);}
    friend std::istream &operator>>(std::istream &in,bigint &a){
        std::string s;
        in>>s;a=bigint(s);
        return in;
    }
    friend std::ostream &operator<<(std::ostream &out,const bigint &a){
        if(a.is_negative) out<<'-';
        out<<a.num.back();
        for(int i=int(a.num.size())-2;i>=0;i--)
            out<<std::setw(DIGITS_PER_BASE)<<std::setfill('0')<<a.num[i];
        return out;
    }
    bool operator<(const bigint &x)const{
        if(is_negative!=x.is_negative)
            return is_negative>x.is_negative;
        if(num.size()!=x.num.size())
            return is_negative?num.size()>x.num.size():num.size()<x.num.size();
        for(int i=int(num.size())-1;i>=0;i--)
            if(num[i]!=x.num[i])
                return is_negative?num[i]>x.num[i]:num[i]<x.num[i];
        return false;
    }
    inline bigint abs()const{
        bigint res=*this;res.is_negative=false;
        return res;
    }
    bigint(const std::string &s){
        if(!s.length()){
            std::cerr<<"Error:An invalid number!\n";
            return;
        }
        num.clear(),is_negative=false;
        int low=0;
        if(s[0]=='-') low=1,is_negative=true;
        int base_num=0,base_w=1;
        for(int i=int(s.length())-1;i>=low;i--){
            if(s[i]<'0'||s[i]>'9'){
                std::cerr<<"Error:An invalid number!\n";
                return;
            }
            base_num+=(s[i]^48)*base_w;
            base_w*=10;
            if(base_w==BASE||i==low){
                num.push_back(base_num);
                base_num=0,base_w=1;
            }
        }
        if(!num.size()) std::cerr<<"Error:An invalid number!\n";
        if(num.size()==1&&num.back()==0&&is_negative)
            std::cerr<<"Error:An invalid number!\n";
    }
    inline bigint operator+(const bigint &x)const{
        bigint res;
        if(is_negative==x.is_negative){
            res.is_negative=is_negative;
            res.num.resize(std::max(num.size(),x.num.size()));
            int carry=0;
            for(int i=0;i<int(res.num.size());i++){
                int sum=carry;
                if(i<int(num.size())) sum+=num[i];
                if(i<int(x.num.size())) sum+=x.num[i];
                res.num[i]=sum%BASE;
                carry=sum/BASE;
            }
            if(carry) res.num.push_back(carry);
        }
        else{
            int cmp=cmp_abs(*this,x);
            const bigint &larger=cmp>=0?*this:x;
            const bigint &smaller=cmp>=0?x:*this;
            res.is_negative=cmp>=0?is_negative:x.is_negative;
            res.num.resize(larger.num.size());
            int borrow=0;
            for(int i=0;i<int(res.num.size());i++){
                int diff=larger.num[i]-borrow;
                if(i<int(smaller.num.size())) diff-=smaller.num[i];
                if(diff<0){
                    diff+=BASE;
                    borrow=1;
                }
                else borrow=0;
                res.num[i]=diff;
            }
            int len=res.num.size();
            while(len>1&&res.num[len]==0) --len;
            res.num.resize(len);
            if(res.num.size()==1&&res.num[0]==0)
                res.is_negative=0;
        }
        return res;
    }
    bigint operator*(const bigint &x)const{
        bigint res;
        res.is_negative=(is_negative!=x.is_negative);
        int len=1;while(len<int(num.size()+x.num.size())) len<<=1;
        std::vector<__FFT::complex> fa(len),fb(len);
        for(int i=0;i<int(num.size());i++)
            fa[i]={double(num[i]),0};
        for(int i=0;i<int(x.num.size());i++)
            fb[i]={double(x.num[i]),0};
        __FFT::init_omega(len);
        __FFT::FFT(fa,len,false);
        __FFT::FFT(fb,len,false);
        for(int i=0;i<len;i++)
            fa[i]=fa[i]*fb[i];
        __FFT::FFT(fa,len,true);
        res.num.resize(len+1);
        int carry=0;
        for(int i=0;i<len;i++){
            long long val=round(fa[i].real)+carry;
            res.num[i]=val%BASE;
            carry=val/BASE;
        }
        if(carry) res.num[len]=carry;
        while(len>1&&res.num[len-1]==0) --len;
        res.num.resize(len);
        if(res.num.size()==1&&res.num[0]==0)
            res.is_negative=false;
        return res;
    }
};
