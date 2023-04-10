include "ke.mm";
include "kc.mm";
include "kt.mm";
include "hb.mm";
include "ht.mm";
include "weq.mm";
include "ax-refl.mm";
include "ax-cb1.mm";

theorem wtru() {





  do {
    ke;
    ke;
    kc;
    ke;
    kc;
    kt;
    hb;
    hb;
    hb;
    ht;
    ht;
    ke;
    hb;
    weq;
    ax-refl;
    ax-cb1;
  };

  return $|- T. : bool$;
}
