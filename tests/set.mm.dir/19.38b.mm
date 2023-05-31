include "wnf.mm";
include "wex.mm";
include "wal.mm";
include "wi.mm";
include "19.38.mm";
include "exim.mm";
include "id.mm";
include "nfrd.mm";
include "syl9r.mm";
include "impbid2.mm";

theorem 19.38b(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {





  do {
    wps;
    vx;
    wnf;
    #;
    wph;
    vx;
    wex;
    #;
    wps;
    vx;
    wal;
    #;
    wi;
    wph;
    wps;
    wi;
    vx;
    wal;
    #;
    wph;
    wps;
    vx;
    19.38;
    @3;
    @1;
    wps;
    vx;
    wex;
    @0;
    @2;
    wph;
    wps;
    vx;
    exim;
    @0;
    wps;
    vx;
    @0;
    id;
    nfrd;
    syl9r;
    impbid2;
  };

  return $|-$ $( F/ x ps -> ( ( E. x ph -> A. x ps ) <-> A. x ( ph -> ps ) ) )$;
}
