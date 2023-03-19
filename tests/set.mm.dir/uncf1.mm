include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "cevlf.mm"
include "c1stf.mm"
include "ccofu.mm"
include "c2ndf.mm"
include "cprf.mm"
include "cop.mm"
include "uncfval.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "df-ov.mm"
include "cxp.mm"
include "cxpc.mm"
include "cfuc.mm"
include "eqid.mm"
include "xpcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "cfunc.mm"
include "wa.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "1stfcl.mm"
include "cofucl.mm"
include "2ndfcl.mm"
include "prfcl.mm"
include "evlfcl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "cofu1.mm"
include "syl5eq.mm"
include "chom.mm"
include "prf1.mm"
include "1stf1.mm"
include "wceq.mm"
include "op1stg.mm"
include "eqtrd.mm"
include "c2nd.mm"
include "2ndf1.mm"
include "op2ndg.mm"
include "opeq12d.mm"
include "syl6eqr.mm"
include "fucbas.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "evlf1.mm"
include "3eqtrd.mm"

theorem uncf1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume uncfval.g: |- F = ( <" C D E "> uncurryF G )
  assume uncfval.c: |- ( ph -> D e. Cat )
  assume uncfval.d: |- ( ph -> E e. Cat )
  assume uncfval.f: |- ( ph -> G e. ( C Func ( D FuncCat E ) ) )
  assume uncf1.a: |- A = ( Base ` C )
  assume uncf1.b: |- B = ( Base ` D )
  assume uncf1.x: |- ( ph -> X e. A )
  assume uncf1.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X ( 1st ` F ) Y ) = ( ( 1st ` ( ( 1st ` G ) ` X ) ) ` Y ) )

  proof
    wph
    cX
    cY
    cF
    c1st
    cfv
    #
    co
    cX
    cY
    cD
    cE
    cevlf
    co
    #
    cG
    cC
    cD
    c1stf
    co
    #
    ccofu
    co
    #
    cC
    cD
    c2ndf
    co
    #
    cprf
    co
    #
    ccofu
    co
    #
    c1st
    cfv
    #
    co
    #
    cX
    cY
    cop
    #
    @5
    c1st
    cfv
    cfv
    #
    @1
    c1st
    cfv
    #
    cfv
    #
    cY
    cX
    cG
    c1st
    cfv
    #
    cfv
    #
    c1st
    cfv
    cfv
    #
    wph
    @0
    @7
    cX
    cY
    wph
    cF
    @6
    c1st
    wph
    cC
    cD
    cE
    cF
    cG
    uncfval.g
    uncfval.c
    uncfval.d
    uncfval.f
    uncfval
    fveq2d
    oveqd
    wph
    @8
    @9
    @7
    cfv
    @12
    cX
    cY
    @7
    df-ov
    wph
    cA
    cB
    cxp
    #
    cC
    cD
    cxpc
    co
    #
    cD
    cE
    cfuc
    co
    #
    cD
    cxpc
    co
    #
    cE
    @5
    @1
    @9
    cC
    cD
    @17
    cA
    cB
    @17
    eqid
    #
    uncf1.a
    uncf1.b
    xpcbas
    #
    wph
    @17
    @18
    @5
    @19
    cD
    @3
    @4
    @5
    eqid
    #
    @19
    eqid
    wph
    @17
    cC
    @18
    @2
    cG
    wph
    cC
    cD
    @2
    @17
    @20
    wph
    cC
    ccat
    wcel
    #
    @18
    ccat
    wcel
    #
    wph
    cG
    cC
    @18
    cfunc
    co
    #
    wcel
    #
    @23
    @24
    wa
    uncfval.f
    cC
    @18
    cG
    funcrcl
    syl
    simpld
    #
    uncfval.c
    @2
    eqid
    #
    1stfcl
    #
    uncfval.f
    cofucl
    #
    wph
    cC
    cD
    @4
    @17
    @20
    @27
    uncfval.c
    @4
    eqid
    #
    2ndfcl
    #
    prfcl
    wph
    cD
    cE
    @18
    @1
    @1
    eqid
    #
    @18
    eqid
    #
    uncfval.c
    uncfval.d
    evlfcl
    wph
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    @9
    @16
    wcel
    uncf1.x
    uncf1.y
    cX
    cY
    cA
    cB
    opelxpi
    syl2anc
    #
    cofu1
    syl5eq
    wph
    @12
    @14
    cY
    @11
    co
    #
    @15
    wph
    @12
    @14
    cY
    cop
    #
    @11
    cfv
    @38
    wph
    @10
    @39
    @11
    wph
    @10
    @9
    @3
    c1st
    cfv
    cfv
    #
    @9
    @4
    c1st
    cfv
    cfv
    #
    cop
    @39
    wph
    @16
    @17
    @18
    @5
    cD
    @3
    @4
    @17
    chom
    cfv
    #
    @9
    @22
    @21
    @42
    eqid
    #
    @30
    @32
    @37
    prf1
    wph
    @40
    @14
    @41
    cY
    wph
    @40
    @9
    @2
    c1st
    cfv
    cfv
    #
    @13
    cfv
    @14
    wph
    @16
    @17
    cC
    @18
    @2
    cG
    @9
    @21
    @29
    uncfval.f
    @37
    cofu1
    wph
    @44
    cX
    @13
    wph
    @44
    @9
    c1st
    cfv
    #
    cX
    wph
    @16
    cC
    cD
    @2
    @9
    @17
    @42
    @20
    @21
    @43
    @27
    uncfval.c
    @28
    @37
    1stf1
    wph
    @35
    @36
    @45
    cX
    wceq
    uncf1.x
    uncf1.y
    cX
    cY
    cA
    cB
    op1stg
    syl2anc
    eqtrd
    fveq2d
    eqtrd
    wph
    @41
    @9
    c2nd
    cfv
    #
    cY
    wph
    @16
    cC
    cD
    @4
    @9
    @17
    @42
    @20
    @21
    @43
    @27
    uncfval.c
    @31
    @37
    2ndf1
    wph
    @35
    @36
    @46
    cY
    wceq
    uncf1.x
    uncf1.y
    cX
    cY
    cA
    cB
    op2ndg
    syl2anc
    eqtrd
    opeq12d
    eqtrd
    fveq2d
    @14
    cY
    @11
    df-ov
    syl6eqr
    wph
    cB
    cD
    cE
    @1
    @14
    cY
    @33
    uncfval.c
    uncfval.d
    uncf1.b
    wph
    cA
    cD
    cE
    cfunc
    co
    #
    cX
    @13
    wph
    cA
    @47
    cC
    @18
    @13
    cG
    c2nd
    cfv
    #
    uncf1.a
    cD
    cE
    @18
    @34
    fucbas
    wph
    @25
    wrel
    @26
    @13
    @48
    @25
    wbr
    cC
    @18
    relfunc
    uncfval.f
    cG
    @25
    1st2ndbr
    sylancr
    funcf1
    uncf1.x
    ffvelrnd
    uncf1.y
    evlf1
    eqtrd
    3eqtrd
end
