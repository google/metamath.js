include "wid5.mm";
include "wi1.mm";
include "lem3.3.3lem1.mm";
include "lem3.3.3lem2.mm";
include "ler2an.mm";

theorem lem3.3.3lem3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wid5;
    wva;
    wvb;
    wi1;
    wvb;
    wva;
    wi1;
    wva;
    wvb;
    lem3.3.3lem1;
    wva;
    wvb;
    lem3.3.3lem2;
    ler2an;
  };

  return $|-$ $( a ==5 b ) =< ( ( a ->1 b ) ^ ( b ->1 a ) )$;
}
