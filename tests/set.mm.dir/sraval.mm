include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cnx.mm"
include "csca.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cip.mm"
include "cpw.mm"
include "csra.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "fveq2.mm"
include "pweqd.mm"
include "id.mm"
include "oveq1.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "df-sra.mm"
include "fvex.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem sraval
  let cS: class S
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vw: setvar w


  assert |- ( ( W e. V /\ S C_ ( Base ` W ) ) -> ( ( subringAlg ` W ) ` S ) = ( ( ( W sSet <. ( Scalar ` ndx ) , ( W |`s S ) >. ) sSet <. ( .s ` ndx ) , ( .r ` W ) >. ) sSet <. ( .i ` ndx ) , ( .r ` W ) >. ) )

  proof
    cW
    cV
    wcel
    #
    cS
    cW
    cbs
    cfv
    #
    wss
    #
    wa
    #
    vs
    cS
    cW
    cnx
    csca
    cfv
    #
    cW
    vs
    cv
    #
    cress
    co
    #
    cop
    #
    csts
    co
    #
    cnx
    cvsca
    cfv
    #
    cW
    cmulr
    cfv
    #
    cop
    #
    csts
    co
    #
    cnx
    cip
    cfv
    #
    @10
    cop
    #
    csts
    co
    #
    cW
    @4
    cW
    cS
    cress
    co
    #
    cop
    #
    csts
    co
    #
    @11
    csts
    co
    #
    @14
    csts
    co
    @1
    cpw
    #
    cW
    csra
    cfv
    #
    cvv
    @3
    cW
    cvv
    wcel
    #
    @21
    vs
    @20
    @15
    cmpt
    #
    wceq
    @0
    @22
    @2
    cW
    cV
    elex
    adantr
    vw
    cW
    vs
    vw
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @24
    @4
    @24
    @5
    cress
    co
    #
    cop
    #
    csts
    co
    #
    @9
    @24
    cmulr
    cfv
    #
    cop
    #
    csts
    co
    #
    @13
    @30
    cop
    #
    csts
    co
    #
    cmpt
    @23
    cvv
    csra
    @24
    cW
    wceq
    #
    vs
    @26
    @34
    @20
    @15
    @35
    @25
    @1
    @24
    cW
    cbs
    fveq2
    pweqd
    @35
    @32
    @12
    @33
    @14
    csts
    @35
    @29
    @8
    @31
    @11
    csts
    @35
    @24
    cW
    @28
    @7
    csts
    @35
    id
    @35
    @27
    @6
    @4
    @24
    cW
    @5
    cress
    oveq1
    opeq2d
    oveq12d
    @35
    @30
    @10
    @9
    @24
    cW
    cmulr
    fveq2
    #
    opeq2d
    oveq12d
    @35
    @30
    @10
    @13
    @36
    opeq2d
    oveq12d
    mpteq12dv
    vw
    vs
    df-sra
    vs
    @20
    @15
    @1
    cW
    cbs
    fvex
    #
    pwex
    mptex
    fvmpt
    syl
    @3
    @5
    cS
    wceq
    #
    wa
    #
    @12
    @19
    @14
    csts
    @39
    @8
    @18
    @11
    csts
    @39
    @7
    @17
    cW
    csts
    @39
    @6
    @16
    @4
    @39
    @5
    cS
    cW
    cress
    @3
    @38
    simpr
    oveq2d
    opeq2d
    oveq2d
    oveq1d
    oveq1d
    @3
    @2
    cS
    @20
    wcel
    @0
    @2
    simpr
    cS
    @1
    @37
    elpw2
    sylibr
    @3
    @19
    @14
    csts
    ovexd
    fvmptd
end
