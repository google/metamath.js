include "wn.mm"
include "wa.mm"
include "jaoi.mm"
include "jaoi2.mm"

theorem jaoi3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jaoi3.1: |- ( ph -> ps )
  assume jaoi3.2: |- ( ( -. ph /\ ch ) -> ps )


  assert |- ( ( ph \/ ch ) -> ps )

  proof
    wph
    wps
    wch
    wph
    wps
    wph
    wn
    wch
    wa
    jaoi3.1
    jaoi3.2
    jaoi
    jaoi2
end
