include "wfal.mm"
include "wi.mm"
include "wn.mm"
include "ex.mm"
include "dfnot.mm"
include "sylibr.mm"

theorem inegd
  let wph: wff ph
  let wps: wff ps
  assume inegd.1: |- ( ( ph /\ ps ) -> F. )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wfal
    wi
    wps
    wn
    wph
    wps
    wfal
    inegd.1
    ex
    wps
    dfnot
    sylibr
end
