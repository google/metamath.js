include "wf.mm";
include "wo.mm";
include "ax-a2.mm";
include "or0.mm";
include "ax-r2.mm";

theorem or0r(wva: $term$ a) {





  do {
    wf;
    wva;
    wo;
    wva;
    wf;
    wo;
    wva;
    wf;
    wva;
    ax-a2;
    wva;
    or0;
    ax-r2;
  };

  return $|-$ $( 0 v a ) = a$;
}
