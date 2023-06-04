include "c2.mm";
include "c1.mm";
include "caddc.mm";
include "co.mm";
include "cc.mm";
include "df-2.mm";
include "ax-1cn.mm";
include "addcli.mm";
include "eqeltri.mm";

theorem 2cn() {





  do {
    c2;
    c1;
    c1;
    caddc;
    co;
    cc;
    df-2;
    c1;
    c1;
    ax-1cn;
    ax-1cn;
    addcli;
    eqeltri;
  };

  return '|-' "2 e. CC";
}
