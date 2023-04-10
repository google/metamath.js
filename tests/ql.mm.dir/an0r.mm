include "wf.mm";
include "wa.mm";
include "ancom.mm";
include "an0.mm";
include "ax-r2.mm";

theorem an0r(wva: $term$ a) {





  do {
    wf;
    wva;
    wa;
    wva;
    wf;
    wa;
    wf;
    wf;
    wva;
    ancom;
    wva;
    an0;
    ax-r2;
  };

  return $|-$ $( 0 ^ a ) = 0$;
}
