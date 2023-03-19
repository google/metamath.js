include "wo.mm"
include "wn.mm"
include "wa.mm"
include "pm5.63.mm"
include "sylbi.mm"

theorem jaoi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jaoi2.1: |- ( ( ph \/ ( -. ph /\ ch ) ) -> ps )


  assert |- ( ( ph \/ ch ) -> ps )

  proof
    wph
    wch
    wo
    wph
    wph
    wn
    wch
    wa
    wo
    wps
    wph
    wch
    pm5.63
    jaoi2.1
    sylbi
end
