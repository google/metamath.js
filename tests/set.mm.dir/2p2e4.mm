include "c2.mm";
include "caddc.mm";
include "co.mm";
include "c1.mm";
include "c4.mm";
include "df-2.mm";
include "oveq2i.mm";
include "c3.mm";
include "df-4.mm";
include "df-3.mm";
include "oveq1i.mm";
include "2cn.mm";
include "ax-1cn.mm";
include "addassi.mm";
include "3eqtri.mm";
include "eqtr4i.mm";

theorem 2p2e4() {





  do {
    c2;
    c2;
    caddc;
    co;
    c2;
    c1;
    c1;
    caddc;
    co;
    #;
    caddc;
    co;
    #;
    c4;
    c2;
    @0;
    c2;
    caddc;
    df-2;
    oveq2i;
    c4;
    c3;
    c1;
    caddc;
    co;
    c2;
    c1;
    caddc;
    co;
    #;
    c1;
    caddc;
    co;
    @1;
    df-4;
    c3;
    @2;
    c1;
    caddc;
    df-3;
    oveq1i;
    c2;
    c1;
    c1;
    2cn;
    ax-1cn;
    ax-1cn;
    addassi;
    3eqtri;
    eqtr4i;
  };

  return '|-' "( 2 + 2 ) = 4";
}
