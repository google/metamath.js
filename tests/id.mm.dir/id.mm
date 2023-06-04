include "wi.mm";
include "ax-1.mm";
include "mpd.mm";

theorem id(wph: 'wff' ph) {





  do {
    wph;
    wph;
    wph;
    wi;
    #;
    wph;
    wph;
    wph;
    ax-1;
    wph;
    @0;
    ax-1;
    mpd;
  };

  return '|-' "( ph -> ph )";
}
