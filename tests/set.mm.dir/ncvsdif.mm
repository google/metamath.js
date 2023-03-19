include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "csg.mm"
include "cclm.mm"
include "wceq.mm"
include "elin.mm"
include "id.mm"
include "cvsclm.mm"
include "simplbiim.mm"
include "csca.mm"
include "eqid.mm"
include "clmvsubval.mm"
include "eqcomd.mm"
include "syl3an1.mm"
include "fveq2d.mm"
include "cngp.mm"
include "wa.mm"
include "cnlm.mm"
include "nvcnlm.mm"
include "nlmngp.mm"
include "syl.mm"
include "adantr.mm"
include "sylbi.mm"
include "nmsub.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "simp2.mm"
include "syl3anc.mm"
include "3eqtrd.mm"

theorem ncvsdif
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cN: class N
  let cV: class V
  let cW: class W
  assume ncvsprp.v: |- V = ( Base ` W )
  assume ncvsprp.n: |- N = ( norm ` W )
  assume ncvsprp.s: |- .x. = ( .s ` W )
  assume ncvsdif.p: |- .+ = ( +g ` W )


  assert |- ( ( W e. ( NrmVec i^i CVec ) /\ A e. V /\ B e. V ) -> ( N ` ( A .+ ( -u 1 .x. B ) ) ) = ( N ` ( B .+ ( -u 1 .x. A ) ) ) )

  proof
    cW
    cnvc
    ccvs
    cin
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    c1
    cneg
    #
    cB
    c.x
    co
    c.pl
    co
    #
    cN
    cfv
    cA
    cB
    cW
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cB
    cA
    @6
    co
    #
    cN
    cfv
    #
    cB
    @4
    cA
    c.x
    co
    c.pl
    co
    #
    cN
    cfv
    @3
    @5
    @7
    cN
    @0
    cW
    cclm
    wcel
    #
    @1
    @2
    @5
    @7
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
    @12
    cW
    cnvc
    ccvs
    elin
    #
    @14
    cW
    @14
    id
    cvsclm
    simplbiim
    #
    @12
    @1
    @2
    w3a
    @7
    @5
    cA
    cB
    c.pl
    c.x
    cW
    csca
    cfv
    #
    @6
    cV
    cW
    ncvsprp.v
    ncvsdif.p
    @6
    eqid
    #
    @17
    eqid
    #
    ncvsprp.s
    clmvsubval
    eqcomd
    syl3an1
    fveq2d
    @0
    cW
    cngp
    wcel
    #
    @1
    @2
    @8
    @10
    wceq
    @0
    @13
    @14
    wa
    @20
    @15
    @13
    @20
    @14
    @13
    cW
    cnlm
    wcel
    @20
    cW
    nvcnlm
    cW
    nlmngp
    syl
    adantr
    sylbi
    cA
    cB
    cW
    @6
    cN
    cV
    ncvsprp.v
    ncvsprp.n
    @18
    nmsub
    syl3an1
    @3
    @9
    @11
    cN
    @3
    @12
    @2
    @1
    @9
    @11
    wceq
    @0
    @1
    @12
    @2
    @16
    3ad2ant1
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    cB
    cA
    c.pl
    c.x
    @17
    @6
    cV
    cW
    ncvsprp.v
    ncvsdif.p
    @18
    @19
    ncvsprp.s
    clmvsubval
    syl3anc
    fveq2d
    3eqtrd
end
