include "id.mm";
include "impbii.mm";

theorem biid(wph: 'wff' ph) {





  do {
    wph;
    wph;
    wph;
    id;
    #;
    @0;
    impbii;
  };

  return '|-' "( ph <-> ph )";
}
