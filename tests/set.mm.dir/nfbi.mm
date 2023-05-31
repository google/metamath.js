include "wb.mm";
include "wnf.mm";
include "wtru.mm";
include "a1i.mm";
include "nfbid.mm";
include "mptru.mm";

theorem nfbi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume nf.1: $|- F/ x ph$;
  assume nf.2: $|- F/ x ps$;





  do {
    wph;
    wps;
    wb;
    vx;
    wnf;
    wtru;
    wph;
    wps;
    vx;
    wph;
    vx;
    wnf;
    wtru;
    nf.1;
    a1i;
    wps;
    vx;
    wnf;
    wtru;
    nf.2;
    a1i;
    nfbid;
    mptru;
  };

  return $|-$ $F/ x ( ph <-> ps )$;
}
