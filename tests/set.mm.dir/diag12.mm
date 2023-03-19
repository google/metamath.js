include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "c1stf.mm"
include "ccurf.mm"
include "c1st.mm"
include "diagval.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "eqid.mm"
include "cxpc.mm"
include "1stfcl.mm"
include "curf12.mm"
include "chom.mm"
include "cres.mm"
include "df-ov.mm"
include "cxp.mm"
include "xpcbas.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "1stf2.mm"
include "wceq.mm"
include "catidcl.mm"
include "xpchom2.mm"
include "eleqtrrd.mm"
include "fvres.mm"
include "syl.mm"
include "op1stg.mm"
include "3eqtrd.mm"

theorem diag12
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.1: class .1.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vd: setvar d
  assume diagval.l: |- L = ( C DiagFunc D )
  assume diagval.c: |- ( ph -> C e. Cat )
  assume diagval.d: |- ( ph -> D e. Cat )
  assume diag11.a: |- A = ( Base ` C )
  assume diag11.c: |- ( ph -> X e. A )
  assume diag11.k: |- K = ( ( 1st ` L ) ` X )
  assume diag11.b: |- B = ( Base ` D )
  assume diag11.y: |- ( ph -> Y e. B )
  assume diag12.j: |- J = ( Hom ` D )
  assume diag12.i: |- .1. = ( Id ` C )
  assume diag12.z: |- ( ph -> Z e. B )
  assume diag12.f: |- ( ph -> F e. ( Y J Z ) )


  assert |- ( ph -> ( ( Y ( 2nd ` K ) Z ) ` F ) = ( .1. ` X ) )

  proof
    wph
    cF
    cY
    cZ
    cK
    c2nd
    cfv
    #
    co
    #
    cfv
    cF
    cY
    cZ
    cX
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
    c1st
    cfv
    #
    cfv
    #
    c2nd
    cfv
    #
    co
    #
    cfv
    cX
    c.1
    cfv
    #
    cF
    cX
    cY
    cop
    #
    cX
    cZ
    cop
    #
    @2
    c2nd
    cfv
    co
    #
    co
    #
    @8
    wph
    cF
    @1
    @7
    wph
    @0
    @6
    cY
    cZ
    wph
    cK
    @5
    c2nd
    wph
    cK
    cX
    cL
    c1st
    cfv
    #
    cfv
    @5
    diag11.k
    wph
    cX
    @13
    @4
    wph
    cL
    @3
    c1st
    wph
    cC
    cD
    cL
    diagval.l
    diagval.c
    diagval.d
    diagval
    fveq2d
    fveq1d
    syl5eq
    fveq2d
    oveqd
    fveq1d
    wph
    cA
    cB
    cC
    cD
    c.1
    cC
    @2
    @3
    cF
    cJ
    @5
    cX
    cY
    cZ
    @3
    eqid
    diag11.a
    diagval.c
    diagval.d
    wph
    cC
    cD
    @2
    cC
    cD
    cxpc
    co
    #
    @14
    eqid
    #
    diagval.c
    diagval.d
    @2
    eqid
    #
    1stfcl
    diag11.b
    diag11.c
    @5
    eqid
    diag11.y
    diag12.j
    diag12.i
    diag12.z
    diag12.f
    curf12
    wph
    @12
    @8
    cF
    cop
    #
    c1st
    @9
    @10
    @14
    chom
    cfv
    #
    co
    #
    cres
    #
    cfv
    #
    @17
    c1st
    cfv
    #
    @8
    wph
    @12
    @17
    @11
    cfv
    @21
    @8
    cF
    @11
    df-ov
    wph
    @17
    @11
    @20
    wph
    cA
    cB
    cxp
    #
    cC
    cD
    @2
    @9
    @10
    @14
    @18
    @15
    cC
    cD
    @14
    cA
    cB
    @15
    diag11.a
    diag11.b
    xpcbas
    @18
    eqid
    #
    diagval.c
    diagval.d
    @16
    wph
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    @9
    @23
    wcel
    diag11.c
    diag11.y
    cX
    cY
    cA
    cB
    opelxpi
    syl2anc
    wph
    @25
    cZ
    cB
    wcel
    @10
    @23
    wcel
    diag11.c
    diag12.z
    cX
    cZ
    cA
    cB
    opelxpi
    syl2anc
    1stf2
    fveq1d
    syl5eq
    wph
    @17
    @19
    wcel
    @21
    @22
    wceq
    wph
    @17
    cX
    cX
    cC
    chom
    cfv
    #
    co
    #
    cY
    cZ
    cJ
    co
    #
    cxp
    #
    @19
    wph
    @8
    @27
    wcel
    #
    cF
    @28
    wcel
    #
    @17
    @29
    wcel
    wph
    cA
    cC
    c.1
    @26
    cX
    diag11.a
    @26
    eqid
    #
    diag12.i
    diagval.c
    diag11.c
    catidcl
    #
    diag12.f
    @8
    cF
    @27
    @28
    opelxpi
    syl2anc
    wph
    cC
    cD
    cX
    cZ
    @14
    @26
    cJ
    @18
    cX
    cY
    cA
    cB
    @15
    diag11.a
    diag11.b
    @32
    diag12.j
    diag11.c
    diag11.y
    diag11.c
    diag12.z
    @24
    xpchom2
    eleqtrrd
    @17
    @19
    c1st
    fvres
    syl
    wph
    @30
    @31
    @22
    @8
    wceq
    @33
    diag12.f
    @8
    cF
    @27
    @28
    op1stg
    syl2anc
    3eqtrd
    3eqtrd
end
