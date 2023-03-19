include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cnm.mm"
include "cmul.mm"
include "cabs.mm"
include "cnlm.mm"
include "wceq.mm"
include "wa.mm"
include "elin.mm"
include "nvcnlm.mm"
include "adantr.mm"
include "sylbi.mm"
include "eqid.mm"
include "nmvs.mm"
include "syl3an1.mm"
include "cclm.mm"
include "id.mm"
include "cvsclm.mm"
include "simplbiim.mm"
include "clmabs.mm"
include "sylan.mm"
include "3adant3.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem ncvsprp
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume ncvsprp.v: |- V = ( Base ` W )
  assume ncvsprp.n: |- N = ( norm ` W )
  assume ncvsprp.s: |- .x. = ( .s ` W )
  assume ncvsprp.f: |- F = ( Scalar ` W )
  assume ncvsprp.k: |- K = ( Base ` F )


  assert |- ( ( W e. ( NrmVec i^i CVec ) /\ A e. K /\ B e. V ) -> ( N ` ( A .x. B ) ) = ( ( abs ` A ) x. ( N ` B ) ) )

  proof
    cW
    cnvc
    ccvs
    cin
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    c.x
    co
    cN
    cfv
    #
    cA
    cF
    cnm
    cfv
    #
    cfv
    #
    cB
    cN
    cfv
    #
    cmul
    co
    #
    cA
    cabs
    cfv
    #
    @7
    cmul
    co
    @0
    cW
    cnlm
    wcel
    #
    @1
    @2
    @4
    @8
    wceq
    @0
    cW
    cnvc
    wcel
    #
    cW
    ccvs
    wcel
    #
    wa
    @10
    cW
    cnvc
    ccvs
    elin
    #
    @11
    @10
    @12
    cW
    nvcnlm
    adantr
    sylbi
    @5
    c.x
    cF
    cK
    cN
    cV
    cW
    cA
    cB
    ncvsprp.v
    ncvsprp.n
    ncvsprp.s
    ncvsprp.f
    ncvsprp.k
    @5
    eqid
    nmvs
    syl3an1
    @3
    @6
    @9
    @7
    cmul
    @3
    @9
    @6
    @0
    @1
    @9
    @6
    wceq
    #
    @2
    @0
    cW
    cclm
    wcel
    #
    @1
    @14
    @0
    @11
    @12
    @15
    @13
    @12
    cW
    @12
    id
    cvsclm
    simplbiim
    cA
    cF
    cK
    cW
    ncvsprp.f
    ncvsprp.k
    clmabs
    sylan
    3adant3
    eqcomd
    oveq1d
    eqtrd
end
