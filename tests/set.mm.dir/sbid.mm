include "weq.mm";
include "wsb.mm";
include "wb.mm";
include "equid.mm";
include "sbequ12r.mm";
include "ax-mp.mm";

theorem sbid(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    vx;
    vx;
    weq;
    wph;
    vx;
    vx;
    wsb;
    wph;
    wb;
    vx;
    equid;
    wph;
    vx;
    vx;
    sbequ12r;
    ax-mp;
  };

  return $|-$ $( [ x / x ] ph <-> ph )$;
}
