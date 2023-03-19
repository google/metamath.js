include "wtru.mm"
include "wcad.mm"
include "tru.mm"
include "cad11.mm"
include "mp2an.mm"

theorem cadtru
  let wph: wff ph


  assert |- cadd ( T. , T. , ph )

  proof
    wtru
    wtru
    wtru
    wtru
    wph
    wcad
    tru
    tru
    wtru
    wtru
    wph
    cad11
    mp2an
end
