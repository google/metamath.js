include "id.mm"
include "syl2anc.mm"

theorem mpancom
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mpancom.1: |- ( ps -> ph )
  assume mpancom.2: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ps -> ch )

  proof
    wps
    wph
    wps
    wch
    mpancom.1
    wps
    id
    mpancom.2
    syl2anc
end
