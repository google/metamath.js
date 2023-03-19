include "cxp.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "opex.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "opeq12d.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "fnmpti.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fvelimab.mm"
include "sylancr.mm"
include "wa.mm"
include "simp-4r.mm"
include "simplr.mm"
include "opelxpi.mm"
include "simpllr.mm"
include "simpr.mm"
include "ad5antr.mm"
include "sseldd.mm"
include "fvproj.mm"
include "1st2nd2.mm"
include "ad5antlr.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "wfun.mm"
include "ad3antrrr.mm"
include "fnfun.mm"
include "syl.mm"
include "xp2nd.mm"
include "ad3antlr.mm"
include "fvelima.mm"
include "r19.29a.mm"
include "adantr.mm"
include "xp1st.mm"
include "adantl.mm"
include "cvv.mm"
include "ad2antrr.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "r19.29an.mm"
include "impbida.mm"
include "bitr4d.mm"
include "eqrdv.mm"

theorem fimaproj
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  assume fvproj.h: |- H = ( x e. A , y e. B |-> <. ( F ` x ) , ( G ` y ) >. )
  assume fimaproj.f: |- ( ph -> F Fn A )
  assume fimaproj.g: |- ( ph -> G Fn B )
  assume fimaproj.x: |- ( ph -> X C_ A )
  assume fimaproj.y: |- ( ph -> Y C_ B )

  disjoint H x
  disjoint H y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H z
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint x z
  disjoint y z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint ph z
  disjoint A a
  disjoint A b
  disjoint A z
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint x z
  disjoint y z
  disjoint B a
  disjoint B b
  disjoint B z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F z
  disjoint a c
  disjoint b c
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X z
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y z
  assert |- ( ph -> ( H " ( X X. Y ) ) = ( ( F " X ) X. ( G " Y ) ) )

  proof
    wph
    vc
    cH
    cX
    cY
    cxp
    #
    cima
    #
    cF
    cX
    cima
    #
    cG
    cY
    cima
    #
    cxp
    #
    wph
    vc
    cv
    #
    @1
    wcel
    #
    vz
    cv
    #
    cH
    cfv
    #
    @5
    wceq
    #
    vz
    @0
    wrex
    #
    @5
    @4
    wcel
    #
    wph
    cH
    cA
    cB
    cxp
    #
    wfn
    @0
    @12
    wss
    #
    @6
    @10
    wb
    vz
    @12
    @7
    c1st
    cfv
    #
    cF
    cfv
    #
    @7
    c2nd
    cfv
    #
    cG
    cfv
    #
    cop
    #
    cH
    @15
    @17
    opex
    #
    cH
    vx
    vy
    cA
    cB
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cG
    cfv
    #
    cop
    #
    cmpt2
    vz
    @12
    @18
    cmpt
    fvproj.h
    vx
    vy
    vz
    cA
    cB
    @18
    @24
    @7
    @20
    @22
    cop
    wceq
    #
    @15
    @21
    @17
    @23
    @25
    @14
    @20
    cF
    @20
    @22
    @7
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    @25
    @16
    @22
    cG
    @20
    @22
    @7
    @26
    @27
    op2ndd
    fveq2d
    opeq12d
    mpt2mpt
    eqtr4i
    #
    fnmpti
    wph
    cX
    cA
    wss
    #
    cY
    cB
    wss
    #
    @13
    fimaproj.x
    fimaproj.y
    cX
    cA
    cY
    cB
    xpss12
    syl2anc
    #
    vz
    @12
    @0
    @5
    cH
    fvelimab
    sylancr
    wph
    @11
    @10
    wph
    @11
    wa
    #
    va
    cv
    #
    cF
    cfv
    #
    @5
    c1st
    cfv
    #
    wceq
    #
    @10
    va
    cX
    @32
    @33
    cX
    wcel
    #
    wa
    #
    @36
    wa
    #
    vb
    cv
    #
    cG
    cfv
    #
    @5
    c2nd
    cfv
    #
    wceq
    #
    @10
    vb
    cY
    @39
    @40
    cY
    wcel
    #
    wa
    #
    @43
    wa
    #
    @33
    @40
    cop
    #
    @0
    wcel
    #
    @47
    cH
    cfv
    #
    @5
    wceq
    #
    @10
    @46
    @37
    @44
    @48
    @32
    @37
    @36
    @44
    @43
    simp-4r
    #
    @39
    @44
    @43
    simplr
    #
    @33
    @40
    cX
    cY
    opelxpi
    syl2anc
    @46
    @34
    @41
    cop
    @35
    @42
    cop
    #
    @49
    @5
    @46
    @34
    @35
    @41
    @42
    @38
    @36
    @44
    @43
    simpllr
    @45
    @43
    simpr
    opeq12d
    @46
    vx
    vy
    cA
    cB
    cF
    cG
    cH
    @33
    @40
    fvproj.h
    @46
    cX
    cA
    @33
    wph
    @29
    @11
    @37
    @36
    @44
    @43
    fimaproj.x
    ad5antr
    @51
    sseldd
    @46
    cY
    cB
    @40
    wph
    @30
    @11
    @37
    @36
    @44
    @43
    fimaproj.y
    ad5antr
    @52
    sseldd
    fvproj
    @11
    @5
    @53
    wceq
    wph
    @37
    @36
    @44
    @43
    @5
    @2
    @3
    1st2nd2
    ad5antlr
    3eqtr4d
    @9
    @50
    vz
    @47
    @0
    @7
    @47
    wceq
    @8
    @49
    @5
    @7
    @47
    cH
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @39
    cG
    wfun
    #
    @42
    @3
    wcel
    #
    @43
    vb
    cY
    wrex
    @39
    cG
    cB
    wfn
    #
    @54
    wph
    @56
    @11
    @37
    @36
    fimaproj.g
    ad3antrrr
    cB
    cG
    fnfun
    syl
    @11
    @55
    wph
    @37
    @36
    @5
    @2
    @3
    xp2nd
    ad3antlr
    vb
    @42
    cY
    cG
    fvelima
    syl2anc
    r19.29a
    @32
    cF
    wfun
    #
    @35
    @2
    wcel
    #
    @36
    va
    cX
    wrex
    @32
    cF
    cA
    wfn
    #
    @57
    wph
    @59
    @11
    fimaproj.f
    adantr
    cA
    cF
    fnfun
    syl
    @11
    @58
    wph
    @5
    @2
    @3
    xp1st
    adantl
    va
    @35
    cX
    cF
    fvelima
    syl2anc
    r19.29a
    wph
    @9
    @11
    vz
    @0
    wph
    @7
    @0
    wcel
    #
    wa
    #
    @9
    wa
    #
    @8
    @5
    @4
    @61
    @9
    simpr
    @62
    @8
    @18
    @4
    @62
    @7
    @12
    wcel
    @18
    cvv
    wcel
    @8
    @18
    wceq
    @62
    @0
    @12
    @7
    wph
    @13
    @60
    @9
    @31
    ad2antrr
    wph
    @60
    @9
    simplr
    #
    sseldd
    @19
    vz
    @12
    @18
    cvv
    cH
    @28
    fvmpt2
    sylancl
    @62
    @15
    @2
    wcel
    #
    @17
    @3
    wcel
    #
    @18
    @4
    wcel
    @62
    @59
    @29
    @14
    cX
    wcel
    #
    @64
    wph
    @59
    @60
    @9
    fimaproj.f
    ad2antrr
    wph
    @29
    @60
    @9
    fimaproj.x
    ad2antrr
    @62
    @60
    @66
    @63
    @7
    cX
    cY
    xp1st
    syl
    cA
    cX
    cF
    @14
    fnfvima
    syl3anc
    @62
    @56
    @30
    @16
    cY
    wcel
    #
    @65
    wph
    @56
    @60
    @9
    fimaproj.g
    ad2antrr
    wph
    @30
    @60
    @9
    fimaproj.y
    ad2antrr
    @62
    @60
    @67
    @63
    @7
    cX
    cY
    xp2nd
    syl
    cB
    cY
    cG
    @16
    fnfvima
    syl3anc
    @15
    @17
    @2
    @3
    opelxpi
    syl2anc
    eqeltrd
    eqeltrrd
    r19.29an
    impbida
    bitr4d
    eqrdv
end
