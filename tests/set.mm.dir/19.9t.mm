include "wnf.mm";
include "wex.mm";
include "id.mm";
include "19.9d.mm";
include "19.8a.mm";
include "impbid1.mm";

theorem 19.9t(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wnf;
    #;
    wph;
    vx;
    wex;
    wph;
    wph;
    @0;
    vx;
    @0;
    id;
    19.9d;
    wph;
    vx;
    19.8a;
    impbid1;
  };

  return $|-$ $( F/ x ph -> ( E. x ph <-> ph ) )$;
}
