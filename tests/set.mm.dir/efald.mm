include "wn.mm"
include "inegd.mm"
include "notnotrd.mm"

theorem efald
  let wph: wff ph
  let wps: wff ps
  assume efald.1: |- ( ( ph /\ -. ps ) -> F. )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wps
    wn
    efald.1
    inegd
    notnotrd
end
