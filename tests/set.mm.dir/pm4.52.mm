include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "annim.mm"
include "imor.mm"
include "xchbinx.mm"

theorem pm4.52
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) )

  proof
    wph
    wps
    wn
    wa
    wph
    wps
    wi
    wph
    wn
    wps
    wo
    wph
    wps
    annim
    wph
    wps
    imor
    xchbinx
end
