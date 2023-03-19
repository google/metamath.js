include "chl.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "w3a.mm"
include "cdm.mm"
include "cocv.mm"
include "clsm.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "simp2.mm"
include "eqid.mm"
include "pjth.mm"
include "cphl.mm"
include "wa.mm"
include "wb.mm"
include "hlphl.mm"
include "3ad2ant1.mm"
include "pjdm2.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem pjth2
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  assume pjth2.j: |- J = ( TopOpen ` W )
  assume pjth2.l: |- L = ( LSubSp ` W )
  assume pjth2.k: |- K = ( proj ` W )


  assert |- ( ( W e. CHil /\ U e. L /\ U e. ( Clsd ` J ) ) -> U e. dom K )

  proof
    cW
    chl
    wcel
    #
    cU
    cL
    wcel
    #
    cU
    cJ
    ccld
    cfv
    wcel
    #
    w3a
    #
    cU
    cK
    cdm
    wcel
    #
    @1
    cU
    cU
    cW
    cocv
    cfv
    #
    cfv
    cW
    clsm
    cfv
    #
    co
    cW
    cbs
    cfv
    #
    wceq
    #
    @0
    @1
    @2
    simp2
    @6
    cU
    cJ
    cL
    @5
    @7
    cW
    @7
    eqid
    #
    @6
    eqid
    #
    @5
    eqid
    #
    pjth2.j
    pjth2.l
    pjth
    @3
    cW
    cphl
    wcel
    #
    @4
    @1
    @8
    wa
    wb
    @0
    @1
    @12
    @2
    cW
    hlphl
    3ad2ant1
    @6
    cU
    cK
    cL
    @5
    @7
    cW
    @9
    pjth2.l
    @11
    @10
    pjth2.k
    pjdm2
    syl
    mpbir2and
end
