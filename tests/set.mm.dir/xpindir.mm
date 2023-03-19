include "cxp.mm"
include "cin.mm"
include "inxp.mm"
include "inidm.mm"
include "xpeq2i.mm"
include "eqtr2i.mm"

theorem xpindir
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( A i^i B ) X. C ) = ( ( A X. C ) i^i ( B X. C ) )

  proof
    cA
    cC
    cxp
    cB
    cC
    cxp
    cin
    cA
    cB
    cin
    #
    cC
    cC
    cin
    #
    cxp
    @0
    cC
    cxp
    cA
    cC
    cB
    cC
    inxp
    @1
    cC
    @0
    cC
    inidm
    xpeq2i
    eqtr2i
end
