include "ax-syl.mm";

theorem syl(tr: term R, ts: term S, tt: term T) {
  assume ax-syl.1: |- "R |= S";
  assume ax-syl.2: |- "S |= T";





  do {
    tr;
    ts;
    tt;
    ax-syl.1;
    ax-syl.2;
    ax-syl;
  };

  return '|-' "R |= T";
}
