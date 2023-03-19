include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "w3a.mm"
include "lincscmcl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "jca.mm"
include "lincsumcl.mm"
include "syldan.mm"

theorem lincsumscmcl
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cM: class M
  let cV: class V
  let vs: setvar s
  let vv: setvar v
  let vx: setvar x
  let vk: setvar k
  assume lincscmcl.s: |- .x. = ( .s ` M )
  assume lincscmcl.r: |- R = ( Base ` ( Scalar ` M ) )
  assume lincsumscmcl.b: |- .+ = ( +g ` M )


  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ ( C e. R /\ D e. ( M LinCo V ) /\ B e. ( M LinCo V ) ) ) -> ( ( C .x. D ) .+ B ) e. ( M LinCo V ) )

  proof
    cM
    clmod
    wcel
    cV
    cM
    cbs
    cfv
    cpw
    wcel
    wa
    #
    cC
    cR
    wcel
    #
    cD
    cM
    cV
    clinco
    co
    #
    wcel
    #
    cB
    @2
    wcel
    #
    w3a
    #
    cC
    cD
    c.x
    co
    #
    @2
    wcel
    #
    @4
    wa
    @6
    cB
    c.pl
    co
    @2
    wcel
    @0
    @5
    wa
    @7
    @4
    @0
    @1
    @3
    @7
    @4
    cC
    cD
    cR
    c.x
    cM
    cV
    lincscmcl.s
    lincscmcl.r
    lincscmcl
    3adant3r3
    @0
    @1
    @3
    @4
    simpr3
    jca
    @6
    cB
    c.pl
    cM
    cV
    lincsumscmcl.b
    lincsumcl
    syldan
end
