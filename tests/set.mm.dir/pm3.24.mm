include "wi.mm"
include "wn.mm"
include "wa.mm"
include "id.mm"
include "iman.mm"
include "mpbi.mm"

theorem pm3.24
  let wph: wff ph


  assert |- -. ( ph /\ -. ph )

  proof
    wph
    wph
    wi
    wph
    wph
    wn
    wa
    wn
    wph
    id
    wph
    wph
    iman
    mpbi
end
