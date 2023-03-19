include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "csg.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cngp.mm"
include "wceq.mm"
include "wa.mm"
include "elin.mm"
include "cnlm.mm"
include "nvcnlm.mm"
include "nlmngp.mm"
include "syl.mm"
include "adantr.mm"
include "sylbi.mm"
include "eqid.mm"
include "ngpds.mm"
include "syl3an1.mm"
include "cclm.mm"
include "id.mm"
include "cvsclm.mm"
include "simplbiim.mm"
include "csca.mm"
include "clmvsubval.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem ncvspds
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  assume ncvspds.n: |- N = ( norm ` G )
  assume ncvspds.x: |- X = ( Base ` G )
  assume ncvspds.p: |- .+ = ( +g ` G )
  assume ncvspds.d: |- D = ( dist ` G )
  assume ncvspds.s: |- .x. = ( .s ` G )


  assert |- ( ( G e. ( NrmVec i^i CVec ) /\ A e. X /\ B e. X ) -> ( A D B ) = ( N ` ( A .+ ( -u 1 .x. B ) ) ) )

  proof
    cG
    cnvc
    ccvs
    cin
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cD
    co
    #
    cA
    cB
    cG
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cA
    c1
    cneg
    cB
    c.x
    co
    c.pl
    co
    #
    cN
    cfv
    @0
    cG
    cngp
    wcel
    #
    @1
    @2
    @4
    @7
    wceq
    @0
    cG
    cnvc
    wcel
    #
    cG
    ccvs
    wcel
    #
    wa
    @9
    cG
    cnvc
    ccvs
    elin
    #
    @10
    @9
    @11
    @10
    cG
    cnlm
    wcel
    @9
    cG
    nvcnlm
    cG
    nlmngp
    syl
    adantr
    sylbi
    cA
    cB
    cD
    cG
    @5
    cN
    cX
    ncvspds.n
    ncvspds.x
    @5
    eqid
    #
    ncvspds.d
    ngpds
    syl3an1
    @3
    @6
    @8
    cN
    @0
    cG
    cclm
    wcel
    #
    @1
    @2
    @6
    @8
    wceq
    @0
    @10
    @11
    @14
    @12
    @11
    cG
    @11
    id
    cvsclm
    simplbiim
    cA
    cB
    c.pl
    c.x
    cG
    csca
    cfv
    #
    @5
    cX
    cG
    ncvspds.x
    ncvspds.p
    @13
    @15
    eqid
    ncvspds.s
    clmvsubval
    syl3an1
    fveq2d
    eqtrd
end
