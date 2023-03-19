include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "ctopn.mm"
include "wceq.mm"
include "cuni.mm"
include "toponuni.mm"
include "eqimss2.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "topnid.mm"

theorem topontopn
  let cA: class A
  let cJ: class J
  let cK: class K
  assume tsettps.a: |- A = ( Base ` K )
  assume tsettps.j: |- J = ( TopSet ` K )


  assert |- ( J e. ( TopOn ` A ) -> J = ( TopOpen ` K ) )

  proof
    cJ
    cA
    ctopon
    cfv
    wcel
    #
    cJ
    cA
    cpw
    wss
    #
    cJ
    cK
    ctopn
    cfv
    wceq
    @0
    cJ
    cuni
    #
    cA
    wss
    #
    @1
    @0
    cA
    @2
    wceq
    @3
    cA
    cJ
    toponuni
    @2
    cA
    eqimss2
    syl
    cJ
    cA
    sspwuni
    sylibr
    cA
    cJ
    cK
    tsettps.a
    tsettps.j
    topnid
    syl
end
