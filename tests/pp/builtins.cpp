// Checks that builtins are recognized with correct types
/*@
    requires \pow(z,z) == 1;
    requires \is_finite(z);
    requires \is_finite(f);
    requires \is_NaN(z);
    requires \is_NaN(f);
    requires \min(x,y) == 0;
    requires \min(x,y+1) <= x;
    requires \max(x,y+1) <= x;
    requires \abs(y+1) >= x;
    requires \abs(z+1.0) >= x;
    requires \pow(2,x) == 1;
    requires \sqrt(z+1.0) == 0;
    requires \ceil(z) == x;
    requires \floor(z) == x;
    requires \sin(z+1.0) == 0;
    requires \sin(z+1.0) == 0;
    requires \cos(z+1.0) == 0;
    requires \tan(z+1.0) == 0;
    requires \asin(z+1.0) == 0;
    requires \acos(z+1.0) == 0;
    requires \atan(z+1.0) == 0;
    requires \sinh(z+1.0) == 0;
    requires \cosh(z+1.0) == 0;
    requires \tanh(z+1.0) == 0;
//    requires \asinh(z+1.0) == 0;
//	requires \acosh(z+1.0) == 0;
//	requires \atanh(z+1.0) == 0;
	requires \atan2(f,z) == 0;
	requires \hypot(f,z) == 0;
*/
void m(int x, int y, double z, float f) {}
