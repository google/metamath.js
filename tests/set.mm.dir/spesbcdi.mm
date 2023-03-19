include "wsbc.mm"
include "sylibr.mm"
include "spesbcd.mm"

theorem spesbcdi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume spesbcdi.1: |- ( ph -> ps )
  assume spesbcdi.2: |- ( [. A / x ]. ch <-> ps )


  assert |- ( ph -> E. x ch )

  proof
    wph
    wch
    vx
    cA
    wph
    wps
    wch
    vx
    cA
    wsbc
    spesbcdi.1
    spesbcdi.2
    sylibr
    spesbcd
end
