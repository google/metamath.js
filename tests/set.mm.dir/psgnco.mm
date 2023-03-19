include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "ccom.mm"
include "cmul.mm"
include "wceq.mm"
include "eqid.mm"
include "symgov.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "cghm.mm"
include "psgnghm2.mm"
include "cvv.mm"
include "prex.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "ghmlin.mm"
include "syl3an1.mm"
include "eqtr3d.mm"

theorem psgnco
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cG: class G
  let cN: class N
  assume psgninv.s: |- S = ( SymGrp ` D )
  assume psgninv.n: |- N = ( pmSgn ` D )
  assume psgninv.p: |- P = ( Base ` S )


  assert |- ( ( D e. Fin /\ F e. P /\ G e. P ) -> ( N ` ( F o. G ) ) = ( ( N ` F ) x. ( N ` G ) ) )

  proof
    cD
    cfn
    wcel
    #
    cF
    cP
    wcel
    #
    cG
    cP
    wcel
    #
    w3a
    #
    cF
    cG
    cS
    cplusg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cF
    cG
    ccom
    #
    cN
    cfv
    cF
    cN
    cfv
    cG
    cN
    cfv
    cmul
    co
    #
    @3
    @5
    @7
    cN
    @1
    @2
    @5
    @7
    wceq
    @0
    cD
    cP
    @4
    cS
    cF
    cG
    psgninv.s
    psgninv.p
    @4
    eqid
    #
    symgov
    3adant1
    fveq2d
    @0
    cN
    cS
    ccnfld
    cmgp
    cfv
    #
    c1
    c1
    cneg
    #
    cpr
    #
    cress
    co
    #
    cghm
    co
    wcel
    @1
    @2
    @6
    @8
    wceq
    cD
    cS
    @13
    cN
    psgninv.s
    psgninv.n
    @13
    eqid
    #
    psgnghm2
    @4
    cmul
    cS
    @13
    cF
    cN
    cG
    cP
    psgninv.p
    @9
    @12
    cvv
    wcel
    cmul
    @13
    cplusg
    cfv
    wceq
    c1
    @11
    prex
    @12
    cmul
    @10
    @13
    cvv
    @14
    ccnfld
    cmul
    @10
    @10
    eqid
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    ghmlin
    syl3an1
    eqtr3d
end
