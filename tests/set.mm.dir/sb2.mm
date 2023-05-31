include "weq.mm";
include "wi.mm";
include "wal.mm";
include "wa.mm";
include "wex.mm";
include "wsb.mm";
include "sp.mm";
include "equs4.mm";
include "df-sb.mm";
include "sylanbrc.mm";

theorem sb2(wph: $wff$ ph, vx: $setvar$ x, vy: $setvar$ y) {





  do {
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    #;
    vx;
    wal;
    @1;
    @0;
    wph;
    wa;
    vx;
    wex;
    wph;
    vx;
    vy;
    wsb;
    @1;
    vx;
    sp;
    wph;
    vx;
    vy;
    equs4;
    wph;
    vx;
    vy;
    df-sb;
    sylanbrc;
  };

  return $|-$ $( A. x ( x = y -> ph ) -> [ y / x ] ph )$;
}
