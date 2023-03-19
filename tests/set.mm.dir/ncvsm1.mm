include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "csca.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl.mm"
include "elin.mm"
include "cclm.mm"
include "id.mm"
include "cvsclm.mm"
include "eqid.mm"
include "clmneg1.mm"
include "syl.mm"
include "simplbiim.mm"
include "adantr.mm"
include "simpr.mm"
include "ncvsprp.mm"
include "syl3anc.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "cngp.mm"
include "cr.mm"
include "cnlm.mm"
include "nvcnlm.mm"
include "nlmngp.mm"
include "sylbi.mm"
include "nmcl.mm"
include "sylan.mm"
include "recnd.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem ncvsm1
  let cA: class A
  let c.x: class .x.
  let cN: class N
  let cV: class V
  let cW: class W
  assume ncvsprp.v: |- V = ( Base ` W )
  assume ncvsprp.n: |- N = ( norm ` W )
  assume ncvsprp.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. ( NrmVec i^i CVec ) /\ A e. V ) -> ( N ` ( -u 1 .x. A ) ) = ( N ` A ) )

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
    wa
    #
    c1
    cneg
    #
    cA
    c.x
    co
    cN
    cfv
    #
    @3
    cabs
    cfv
    #
    cA
    cN
    cfv
    #
    cmul
    co
    #
    @6
    @2
    @0
    @3
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @1
    @4
    @7
    wceq
    @0
    @1
    simpl
    @0
    @10
    @1
    @0
    cW
    cnvc
    wcel
    #
    cW
    ccvs
    wcel
    #
    @10
    cW
    cnvc
    ccvs
    elin
    #
    @12
    cW
    cclm
    wcel
    @10
    @12
    cW
    @12
    id
    cvsclm
    @8
    @9
    cW
    @8
    eqid
    #
    @9
    eqid
    #
    clmneg1
    syl
    simplbiim
    adantr
    @0
    @1
    simpr
    @3
    cA
    c.x
    @8
    @9
    cN
    cV
    cW
    ncvsprp.v
    ncvsprp.n
    ncvsprp.s
    @14
    @15
    ncvsprp
    syl3anc
    @2
    @7
    c1
    @6
    cmul
    co
    @6
    @5
    c1
    @6
    cmul
    @5
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    @2
    @6
    @2
    @6
    @0
    cW
    cngp
    wcel
    #
    @1
    @6
    cr
    wcel
    @0
    @11
    @12
    wa
    @16
    @13
    @11
    @16
    @12
    @11
    cW
    cnlm
    wcel
    @16
    cW
    nvcnlm
    cW
    nlmngp
    syl
    adantr
    sylbi
    cA
    cW
    cN
    cV
    ncvsprp.v
    ncvsprp.n
    nmcl
    sylan
    recnd
    mulid2d
    syl5eq
    eqtrd
end
