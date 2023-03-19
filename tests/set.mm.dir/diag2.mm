include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "c1stf.mm"
include "ccurf.mm"
include "cv.mm"
include "ccid.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "diagval.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "fveq1d.mm"
include "eqid.mm"
include "cxpc.mm"
include "1stfcl.mm"
include "curf2.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "chom.mm"
include "cres.mm"
include "xpcbas.mm"
include "ccat.mm"
include "adantr.mm"
include "opelxpi.mm"
include "sylan.mm"
include "1stf2.mm"
include "df-ov.mm"
include "wceq.mm"
include "simpr.mm"
include "catidcl.mm"
include "syl2anc.mm"
include "xpchom2.mm"
include "eleqtrrd.mm"
include "fvres.mm"
include "syl.mm"
include "syl5eq.mm"
include "op1stg.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"

theorem diag2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cH: class H
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume diag2.l: |- L = ( C DiagFunc D )
  assume diag2.a: |- A = ( Base ` C )
  assume diag2.b: |- B = ( Base ` D )
  assume diag2.h: |- H = ( Hom ` C )
  assume diag2.c: |- ( ph -> C e. Cat )
  assume diag2.d: |- ( ph -> D e. Cat )
  assume diag2.x: |- ( ph -> X e. A )
  assume diag2.y: |- ( ph -> Y e. A )
  assume diag2.f: |- ( ph -> F e. ( X H Y ) )


  assert |- ( ph -> ( ( X ( 2nd ` L ) Y ) ` F ) = ( B X. { F } ) )

  proof
    wph
    cF
    cX
    cY
    cL
    c2nd
    cfv
    #
    co
    #
    cfv
    cF
    cX
    cY
    cC
    cD
    cop
    cC
    cD
    c1stf
    co
    #
    ccurf
    co
    #
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    vx
    cB
    cF
    vx
    cv
    #
    cD
    ccid
    cfv
    #
    cfv
    #
    cX
    @7
    cop
    #
    cY
    @7
    cop
    #
    @2
    c2nd
    cfv
    co
    #
    co
    #
    cmpt
    #
    cB
    cF
    csn
    cxp
    #
    wph
    cF
    @1
    @5
    wph
    @0
    @4
    cX
    cY
    wph
    cL
    @3
    c2nd
    wph
    cC
    cD
    cL
    diag2.l
    diag2.c
    diag2.d
    diagval
    fveq2d
    oveqd
    fveq1d
    wph
    vx
    cA
    cB
    cC
    cD
    cC
    @2
    @3
    cH
    @8
    cF
    @6
    cX
    cY
    @3
    eqid
    diag2.a
    diag2.c
    diag2.d
    wph
    cC
    cD
    @2
    cC
    cD
    cxpc
    co
    #
    @16
    eqid
    #
    diag2.c
    diag2.d
    @2
    eqid
    #
    1stfcl
    diag2.b
    diag2.h
    @8
    eqid
    #
    diag2.x
    diag2.y
    diag2.f
    @6
    eqid
    curf2
    wph
    @14
    vx
    cB
    cF
    cmpt
    @15
    wph
    vx
    cB
    @13
    cF
    wph
    @7
    cB
    wcel
    #
    wa
    #
    @13
    cF
    @9
    c1st
    @10
    @11
    @16
    chom
    cfv
    #
    co
    #
    cres
    #
    co
    #
    cF
    @9
    cop
    #
    c1st
    cfv
    #
    cF
    @21
    @12
    @24
    cF
    @9
    @21
    cA
    cB
    cxp
    #
    cC
    cD
    @2
    @10
    @11
    @16
    @22
    @17
    cC
    cD
    @16
    cA
    cB
    @17
    diag2.a
    diag2.b
    xpcbas
    @22
    eqid
    #
    wph
    cC
    ccat
    wcel
    @20
    diag2.c
    adantr
    wph
    cD
    ccat
    wcel
    @20
    diag2.d
    adantr
    #
    @18
    wph
    cX
    cA
    wcel
    #
    @20
    @10
    @28
    wcel
    diag2.x
    cX
    @7
    cA
    cB
    opelxpi
    sylan
    wph
    cY
    cA
    wcel
    #
    @20
    @11
    @28
    wcel
    diag2.y
    cY
    @7
    cA
    cB
    opelxpi
    sylan
    1stf2
    oveqd
    @21
    @25
    @26
    @24
    cfv
    #
    @27
    cF
    @9
    @24
    df-ov
    @21
    @26
    @23
    wcel
    @33
    @27
    wceq
    @21
    @26
    cX
    cY
    cH
    co
    #
    @7
    @7
    cD
    chom
    cfv
    #
    co
    #
    cxp
    #
    @23
    @21
    cF
    @34
    wcel
    #
    @9
    @36
    wcel
    #
    @26
    @37
    wcel
    wph
    @38
    @20
    diag2.f
    adantr
    #
    @21
    cB
    cD
    @8
    @35
    @7
    diag2.b
    @35
    eqid
    #
    @19
    @30
    wph
    @20
    simpr
    #
    catidcl
    #
    cF
    @9
    @34
    @36
    opelxpi
    syl2anc
    @21
    cC
    cD
    cY
    @7
    @16
    cH
    @35
    @22
    cX
    @7
    cA
    cB
    @17
    diag2.a
    diag2.b
    diag2.h
    @41
    wph
    @31
    @20
    diag2.x
    adantr
    @42
    wph
    @32
    @20
    diag2.y
    adantr
    @42
    @29
    xpchom2
    eleqtrrd
    @26
    @23
    c1st
    fvres
    syl
    syl5eq
    @21
    @38
    @39
    @27
    cF
    wceq
    @40
    @43
    cF
    @9
    @34
    @36
    op1stg
    syl2anc
    3eqtrd
    mpteq2dva
    vx
    cB
    cF
    fconstmpt
    syl6eqr
    3eqtrd
end
