include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "cfv.mm"
include "cxko.mm"
include "xkotop.mm"
include "syl5eqel.mm"
include "xkouni.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem xkotopon
  let cR: class R
  let cS: class S
  let cJ: class J
  let vf: setvar f
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x
  assume xkouni.1: |- J = ( S ^ko R )


  assert |- ( ( R e. Top /\ S e. Top ) -> J e. ( TopOn ` ( R Cn S ) ) )

  proof
    cR
    ctop
    wcel
    cS
    ctop
    wcel
    wa
    #
    cJ
    ctop
    wcel
    cR
    cS
    ccn
    co
    #
    cJ
    cuni
    wceq
    cJ
    @1
    ctopon
    cfv
    wcel
    @0
    cJ
    cS
    cR
    cxko
    co
    ctop
    xkouni.1
    cR
    cS
    xkotop
    syl5eqel
    cR
    cS
    cJ
    xkouni.1
    xkouni
    @1
    cJ
    istopon
    sylanbrc
end
