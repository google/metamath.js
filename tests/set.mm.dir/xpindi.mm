include "cxp.mm"
include "cin.mm"
include "inxp.mm"
include "inidm.mm"
include "xpeq1i.mm"
include "eqtr2i.mm"

theorem xpindi
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


  assert |- ( A X. ( B i^i C ) ) = ( ( A X. B ) i^i ( A X. C ) )

  proof
    cA
    cB
    cxp
    cA
    cC
    cxp
    cin
    cA
    cA
    cin
    #
    cB
    cC
    cin
    #
    cxp
    cA
    @1
    cxp
    cA
    cB
    cA
    cC
    inxp
    @0
    cA
    @1
    cA
    inidm
    xpeq1i
    eqtr2i
end
