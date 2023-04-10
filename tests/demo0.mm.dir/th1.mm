include "tze.mm";
include "tpl.mm";
include "weq.mm";
include "a2.mm";
include "wim.mm";
include "a1.mm";
include "mp.mm";

theorem th1(tt: $term$ t) {





  do {
    tt;
    tze;
    tpl;
    tt;
    weq;
    tt;
    tt;
    weq;
    tt;
    a2;
    tt;
    tze;
    tpl;
    tt;
    weq;
    tt;
    tze;
    tpl;
    tt;
    weq;
    tt;
    tt;
    weq;
    wim;
    tt;
    a2;
    tt;
    tze;
    tpl;
    tt;
    tt;
    a1;
    mp;
    mp;
  };

  return $|- t = t$;
}
