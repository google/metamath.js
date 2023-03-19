include "wb.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "xor3.mm"
include "pm5.17.mm"
include "bitr4i.mm"

theorem nbi2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) )

  proof
    wph
    wps
    wb
    wn
    wph
    wps
    wn
    wb
    wph
    wps
    wo
    wph
    wps
    wa
    wn
    wa
    wph
    wps
    xor3
    wph
    wps
    pm5.17
    bitr4i
end
