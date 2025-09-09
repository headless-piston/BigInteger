#include<vector>
#include<iostream>
#include<iomanip>
#include<algorithm>
#include<cmath>
#include<stdexcept>
namespace __FFT{
    constexpr double PI2=6.283185307179586231995927;
    struct complex{
        double real,imag;
        complex operator+(const complex &x)const{
            return {real+x.real,imag+x.imag};
        }
        complex operator-(const complex &x)const{
            return {real-x.real,imag-x.imag};
        }
        complex operator*(const complex &x)const{
            return {real*x.real-imag*x.imag,real*x.imag+x.real*imag};
        }
    };
    std::vector<complex> omega;
    void init_omega(const int &n){
        if(n<int(omega.size())) return;
        int start=omega.empty()?1:omega.size()<<1;
        omega.resize(1<<std::__lg(n));
        for(int i=start;i<=n;i<<=1)
            for(int j=0;j<(i>>1);j++){
                double arg=PI2*j/i;
                omega[(i>>1)+j]={cos(arg),sin(arg)};
            }
    }
    void FFT(std::vector<complex> &a,int n,bool inv){
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
    bigint left_shift(const int &k){
        if(num.size()==1&&num[0]==0) return *this;
        num.insert(num.begin(),k,0);
        return *this;
    }
    bigint right_shift(const int &k){
        if(k>=int(num.size())) return *this;
        num.erase(num.begin(),num.begin()+k);
        return *this;
    }
    std::pair<bigint,bigint> div_mod(const bigint &x)const{
        if(x==0) throw std::invalid_argument("Division by zero!");
        if(cmp_abs(*this,x)<0) return {0,*this};
        bigint quo,rem=this->abs();
        quo.num.resize(num.size()-x.num.size()+1);
        for(int i=int(num.size())-int(x.num.size());i>=0;i--){
            int low=0,high=BASE-1,res=0;
            while(low<=high){
                int mid=(low+high)/2;
                bigint prod=x*mid;
                prod.left_shift(i);
                if(cmp_abs(prod,rem)<=0){
                    res=mid;
                    low=mid+1;
                }
                else high=mid-1;
            }
            quo.num[i]=res;
            if(res!=0){
                bigint prod=x.abs()*res;
                prod.left_shift(i);
                rem=rem-prod;
            }
        }
        while(quo.num.size()>1&&quo.num.back()==0) quo.num.pop_back();
        quo.is_negative=is_negative!=x.is_negative;
        if(quo.num.size()==1&&quo.num[0]==0) quo.is_negative=false;
        rem.is_negative=is_negative;
        if(rem.num.size()==1&&rem.num[0]==0) rem.is_negative=false;
        return {quo,rem};
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
    bool operator>(const bigint &x)const{return x<*this;}
    bool operator<=(const bigint &x)const{return !(*this>x);}
    bool operator>=(const bigint &x)const{return !(*this<x);}
    bool operator==(const bigint &x)const{
        if(is_negative!=x.is_negative) return false;
        if(num.size()!=x.num.size()) return false;
        for(int i=0;i<int(num.size());i++)
            if(num[i]!=x.num[i]) return false;
        return true;
    }
    bool operator!=(const bigint &x)const{return !(*this==x);}
    bigint abs()const{
        bigint res=*this;res.is_negative=false;
        return res;
    }
    bigint(long long x){
        num.clear();
        if(x<0) is_negative=true,x=-x;
        else is_negative=false;
        if(x==0) num.push_back(0);
        while(x){
            num.push_back(x%BASE);
            x/=BASE;
        }
    }
    bigint(const std::string &s){
        if(!s.length())
            throw std::invalid_argument("Error:An invalid number!");
        num.clear(),is_negative=false;
        int low=0;
        if(s[0]=='-') low=1,is_negative=true;
        int base_num=0,base_w=1;
        for(int i=int(s.length())-1;i>=low;i--){
            if(s[i]<'0'||s[i]>'9')
                throw std::invalid_argument("Error:An invalid number!");
            base_num+=(s[i]^48)*base_w;
            base_w*=10;
            if(base_w==BASE||i==low){
                num.push_back(base_num);
                base_num=0,base_w=1;
            }
        }
        if(!num.size())
            throw std::invalid_argument("Error:An invalid number!");
        if(num.size()==1&&num.back()==0&&is_negative)
            throw std::invalid_argument("Error:An invalid number!");
    }
    bigint operator-()const{
        bigint res=*this;
        if(res.num.size()==1&&res.num[0]==0)
            res.is_negative=false;
        else res.is_negative=!is_negative;
        return res;
    }
    bigint operator+(const bigint &x)const{
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
            while(res.num.size()>1&&res.num.back()==0) res.num.pop_back();
            if(res.num.size()==1&&res.num[0]==0)
                res.is_negative=0;
        }
        return res;
    }
    bigint operator-(const bigint &x)const{
        bigint temp=x;
        temp.is_negative=!temp.is_negative;
        return *this+temp;
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
        while(res.num.size()>1&&res.num.back()==0) res.num.pop_back();
        if(res.num.size()==1&&res.num[0]==0)
            res.is_negative=false;
        return res;
    }
    bigint operator/(const bigint &x)const{return this->div_mod(x).first;}
    bigint operator%(const bigint &x)const{return this->div_mod(x).second;}
};
