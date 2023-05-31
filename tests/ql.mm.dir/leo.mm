include "wo.mm";
include "anabs.mm";
include "df2le1.mm";

theorem leo(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    anabs;
    df2le1;
  };

  return $|-$ $a =< ( a v b )$;
}
