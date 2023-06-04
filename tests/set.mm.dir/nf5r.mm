include "wex.mm";
include "wnf.mm";
include "wal.mm";
include "19.8a.mm";
include "wi.mm";
include "df-nf.mm";
include "biimpi.mm";
include "syl5.mm";

theorem nf5r(wph: 'wff' ph, vx: 'setvar' x) {





  do {
    wph;
    wph;
    vx;
    wex;
    #;
    wph;
    vx;
    wnf;
    #;
    wph;
    vx;
    wal;
    #;
    wph;
    vx;
    19.8a;
    @1;
    @0;
    @2;
    wi;
    wph;
    vx;
    df-nf;
    biimpi;
    syl5;
  };

  return '|-' "( F/ x ph -> ( ph -> A. x ph ) )";
}
