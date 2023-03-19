include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctopn.mm"
include "ctps.mm"
include "topontopn.mm"
include "id.mm"
include "eqeltrrd.mm"
include "eqid.mm"
include "istps.mm"
include "sylibr.mm"

theorem tsettps
  let cA: class A
  let cJ: class J
  let cK: class K
  assume tsettps.a: |- A = ( Base ` K )
  assume tsettps.j: |- J = ( TopSet ` K )


  assert |- ( J e. ( TopOn ` A ) -> K e. TopSp )

  proof
    cJ
    cA
    ctopon
    cfv
    #
    wcel
    #
    cK
    ctopn
    cfv
    #
    @0
    wcel
    cK
    ctps
    wcel
    @1
    cJ
    @2
    @0
    cA
    cJ
    cK
    tsettps.a
    tsettps.j
    topontopn
    @1
    id
    eqeltrrd
    cA
    @2
    cK
    tsettps.a
    @2
    eqid
    istps
    sylibr
end
