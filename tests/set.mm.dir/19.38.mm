include "wex.mm";
include "wal.mm";
include "wi.mm";
include "wn.mm";
include "alnex.mm";
include "pm2.21.mm";
include "alimi.mm";
include "sylbir.mm";
include "ala1.mm";
include "ja.mm";

theorem 19.38(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wex;
    #;
    wps;
    vx;
    wal;
    wph;
    wps;
    wi;
    #;
    vx;
    wal;
    #;
    @0;
    wn;
    wph;
    wn;
    #;
    vx;
    wal;
    @2;
    wph;
    vx;
    alnex;
    @3;
    @1;
    vx;
    wph;
    wps;
    pm2.21;
    alimi;
    sylbir;
    wps;
    wph;
    vx;
    ala1;
    ja;
  };

  return $|-$ $( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) )$;
}
