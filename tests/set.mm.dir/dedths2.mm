include "wsbc.mm"
include "cif.mm"
include "dfsbcq.mm"
include "dedth.mm"

theorem dedths2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume dedths2.1: |- [. if ( [. A / x ]. ph , A , B ) / x ]. ps


  assert |- ( [. A / x ]. ph -> [. A / x ]. ps )

  proof
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    wps
    vx
    @0
    cA
    cB
    cif
    #
    wsbc
    cA
    cB
    wps
    vx
    cA
    @1
    dfsbcq
    dedths2.1
    dedth
end
