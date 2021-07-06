
void foo (int cnt) {
	int sum = 0;
	switch (cnt) {
	case 0:		do {	sum++;
	default:		sum++;
			} while (--cnt > 0);
	}
}

/*
	Exercise 15 in section 6.6 
	of Stroustrup "The C++ progamming language", 3rd ed. 1997
*/

void send (int* to,int* from,int count) {
	int n = (count + 7) / 8;
		switch (count % 8) {
		case 0:		do {	*to++ = *from++;
		case 7:			*to++ = *from++;
		case 6:			*to++ = *from++;
		case 5:			*to++ = *from++;
		case 4:			*to++ = *from++;
		case 3:			*to++ = *from++;
		case 2:			*to++ = *from++;
		case 1:			*to++ = *from++;
				} while (--n > 0);
		}
}

