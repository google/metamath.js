include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "c1st.mm"
include "ctpos.mm"
include "c2ndf.mm"
include "ccofu.mm"
include "c1stf.mm"
include "cprf.mm"
include "fveq2i.mm"
include "oveqi.mm"
include "df-ov.mm"
include "eqtri.mm"
include "cfunc.mm"
include "cxp.mm"
include "cxpc.mm"
include "coppc.mm"
include "chom.mm"
include "eqid.mm"
include "fucbas.mm"
include "oppcbas.mm"
include "xpcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "cvv.mm"
include "chomf.mm"
include "crn.mm"
include "unssbd.mm"
include "ssexd.mm"
include "setccat.mm"
include "fuccat.mm"
include "2ndfcl.mm"
include "wbr.mm"
include "wrel.mm"
include "relfunc.mm"
include "yoncl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcoppc.mm"
include "df-br.mm"
include "sylib.mm"
include "cofucl.mm"
include "1stfcl.mm"
include "prfcl.mm"
include "unssad.mm"
include "hofcl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "cnat.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "fuchom.mm"
include "xpchom2.mm"
include "eleqtrrd.mm"
include "cofu2.mm"
include "syl5eq.mm"
include "prf1.mm"
include "cofu1.mm"
include "wceq.mm"
include "fvex.mm"
include "tposex.mm"
include "op1st.mm"
include "a1i.mm"
include "2ndf1.mm"
include "op2ndg.mm"
include "eqtrd.mm"
include "fveq12d.mm"
include "1stf1.mm"
include "op1stg.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "prf2.mm"
include "op2nd.mm"
include "ovtpos.mm"
include "cres.mm"
include "2ndf2.mm"
include "fveq1d.mm"
include "fvres.mm"
include "3eqtrd.mm"
include "1stf2.mm"
include "syl6eqr.mm"

theorem yonedalem22
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  let cN: class N
  let cI: class I
  let cM: class M
  assume yoneda.y: |- Y = ( Yon ` C )
  assume yoneda.b: |- B = ( Base ` C )
  assume yoneda.1: |- .1. = ( Id ` C )
  assume yoneda.o: |- O = ( oppCat ` C )
  assume yoneda.s: |- S = ( SetCat ` U )
  assume yoneda.t: |- T = ( SetCat ` V )
  assume yoneda.q: |- Q = ( O FuncCat S )
  assume yoneda.h: |- H = ( HomF ` Q )
  assume yoneda.r: |- R = ( ( Q Xc. O ) FuncCat T )
  assume yoneda.e: |- E = ( O evalF S )
  assume yoneda.z: |- Z = ( H o.func ( ( <. ( 1st ` Y ) , tpos ( 2nd ` Y ) >. o.func ( Q 2ndF O ) ) pairF ( Q 1stF O ) ) )
  assume yoneda.c: |- ( ph -> C e. Cat )
  assume yoneda.w: |- ( ph -> V e. W )
  assume yoneda.u: |- ( ph -> ran ( Homf ` C ) C_ U )
  assume yoneda.v: |- ( ph -> ( ran ( Homf ` Q ) u. U ) C_ V )
  assume yonedalem21.f: |- ( ph -> F e. ( O Func S ) )
  assume yonedalem21.x: |- ( ph -> X e. B )
  assume yonedalem22.g: |- ( ph -> G e. ( O Func S ) )
  assume yonedalem22.p: |- ( ph -> P e. B )
  assume yonedalem22.a: |- ( ph -> A e. ( F ( O Nat S ) G ) )
  assume yonedalem22.k: |- ( ph -> K e. ( P ( Hom ` C ) X ) )


  assert |- ( ph -> ( A ( <. F , X >. ( 2nd ` Z ) <. G , P >. ) K ) = ( ( ( P ( 2nd ` Y ) X ) ` K ) ( <. ( ( 1st ` Y ) ` X ) , F >. ( 2nd ` H ) <. ( ( 1st ` Y ) ` P ) , G >. ) A ) )

  proof
    wph
    cA
    cK
    cF
    cX
    cop
    #
    cG
    cP
    cop
    #
    cZ
    c2nd
    cfv
    #
    co
    #
    co
    #
    cA
    cK
    cop
    #
    @0
    @1
    cY
    c1st
    cfv
    #
    cY
    c2nd
    cfv
    #
    ctpos
    #
    cop
    #
    cQ
    cO
    c2ndf
    co
    #
    ccofu
    co
    #
    cQ
    cO
    c1stf
    co
    #
    cprf
    co
    #
    c2nd
    cfv
    co
    cfv
    #
    @0
    @13
    c1st
    cfv
    #
    cfv
    #
    @1
    @15
    cfv
    #
    cH
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cK
    cP
    cX
    @7
    co
    #
    cfv
    #
    cA
    cX
    @6
    cfv
    #
    cF
    cop
    #
    cP
    @6
    cfv
    #
    cG
    cop
    #
    @18
    co
    #
    co
    #
    wph
    @4
    @5
    @0
    @1
    cH
    @13
    ccofu
    co
    #
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @20
    @4
    cA
    cK
    @31
    co
    @32
    @3
    @31
    cA
    cK
    @2
    @30
    @0
    @1
    cZ
    @29
    c2nd
    yoneda.z
    fveq2i
    oveqi
    oveqi
    cA
    cK
    @31
    df-ov
    eqtri
    wph
    cO
    cS
    cfunc
    co
    #
    cB
    cxp
    #
    cQ
    cO
    cxpc
    co
    #
    cQ
    coppc
    cfv
    #
    cQ
    cxpc
    co
    #
    @5
    cT
    @13
    cH
    @35
    chom
    cfv
    #
    @0
    @1
    cQ
    cO
    @35
    @33
    cB
    @35
    eqid
    #
    cO
    cS
    cQ
    yoneda.q
    fucbas
    #
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    #
    xpcbas
    #
    wph
    @35
    @36
    @13
    @37
    cQ
    @11
    @12
    @13
    eqid
    #
    @37
    eqid
    wph
    @35
    cO
    @36
    @10
    @9
    wph
    cQ
    cO
    @10
    @35
    @39
    wph
    cO
    cS
    cQ
    yoneda.q
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    yoneda.c
    cC
    cO
    yoneda.o
    oppccat
    syl
    #
    wph
    cU
    cvv
    wcel
    cS
    ccat
    wcel
    wph
    cU
    cV
    cW
    yoneda.w
    wph
    cQ
    chomf
    cfv
    crn
    #
    cU
    cV
    yoneda.v
    unssbd
    ssexd
    #
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    fuccat
    #
    @44
    @10
    eqid
    #
    2ndfcl
    #
    wph
    @6
    @8
    cO
    @36
    cfunc
    co
    #
    wbr
    @9
    @50
    wcel
    wph
    cC
    cQ
    @36
    @6
    @7
    cO
    yoneda.o
    @36
    eqid
    #
    wph
    cC
    cQ
    cfunc
    co
    #
    wrel
    cY
    @52
    wcel
    @6
    @7
    @52
    wbr
    cC
    cQ
    relfunc
    wph
    cC
    cQ
    cS
    cU
    cO
    cvv
    cY
    yoneda.y
    yoneda.c
    yoneda.o
    yoneda.s
    yoneda.q
    @46
    yoneda.u
    yoncl
    cY
    @52
    1st2ndbr
    sylancr
    funcoppc
    @6
    @8
    @50
    df-br
    sylib
    #
    cofucl
    #
    wph
    cQ
    cO
    @12
    @35
    @39
    @47
    @44
    @12
    eqid
    #
    1stfcl
    #
    prfcl
    wph
    cQ
    cT
    cV
    cH
    @36
    cW
    yoneda.h
    @51
    yoneda.t
    @47
    yoneda.w
    wph
    @45
    cU
    cV
    yoneda.v
    unssad
    hofcl
    wph
    cF
    @33
    wcel
    #
    cX
    cB
    wcel
    #
    @0
    @34
    wcel
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @33
    cB
    opelxpi
    syl2anc
    #
    wph
    cG
    @33
    wcel
    #
    cP
    cB
    wcel
    #
    @1
    @34
    wcel
    yonedalem22.g
    yonedalem22.p
    cG
    cP
    @33
    cB
    opelxpi
    syl2anc
    #
    @38
    eqid
    #
    wph
    @5
    cF
    cG
    cO
    cS
    cnat
    co
    #
    co
    #
    cX
    cP
    cO
    chom
    cfv
    #
    co
    #
    cxp
    #
    @0
    @1
    @38
    co
    #
    wph
    cA
    @65
    wcel
    #
    cK
    @67
    wcel
    @5
    @68
    wcel
    yonedalem22.a
    wph
    cK
    cP
    cX
    cC
    chom
    cfv
    #
    co
    #
    @67
    yonedalem22.k
    cC
    @71
    cO
    cX
    cP
    @71
    eqid
    yoneda.o
    oppchom
    syl6eleqr
    cA
    cK
    @65
    @67
    opelxpi
    syl2anc
    wph
    cQ
    cO
    cG
    cP
    @35
    @64
    @66
    @38
    cF
    cX
    @33
    cB
    @39
    @40
    @41
    cO
    cS
    cQ
    @64
    yoneda.q
    @64
    eqid
    fuchom
    @66
    eqid
    yonedalem21.f
    yonedalem21.x
    yonedalem22.g
    yonedalem22.p
    @63
    xpchom2
    eleqtrrd
    #
    cofu2
    syl5eq
    wph
    @20
    @22
    cA
    cop
    #
    @27
    cfv
    @28
    wph
    @14
    @74
    @19
    @27
    wph
    @16
    @24
    @17
    @26
    @18
    wph
    @16
    @0
    @11
    c1st
    cfv
    #
    cfv
    #
    @0
    @12
    c1st
    cfv
    #
    cfv
    #
    cop
    @24
    wph
    @34
    @35
    @36
    @13
    cQ
    @11
    @12
    @38
    @0
    @43
    @42
    @63
    @54
    @56
    @59
    prf1
    wph
    @76
    @23
    @78
    cF
    wph
    @76
    @0
    @10
    c1st
    cfv
    #
    cfv
    #
    @9
    c1st
    cfv
    #
    cfv
    @23
    wph
    @34
    @35
    cO
    @36
    @10
    @9
    @0
    @42
    @49
    @53
    @59
    cofu1
    wph
    @80
    cX
    @81
    @6
    @81
    @6
    wceq
    wph
    @6
    @8
    cY
    c1st
    fvex
    #
    @7
    cY
    c2nd
    fvex
    tposex
    #
    op1st
    a1i
    #
    wph
    @80
    @0
    c2nd
    cfv
    #
    cX
    wph
    @34
    cQ
    cO
    @10
    @0
    @35
    @38
    @39
    @42
    @63
    @47
    @44
    @48
    @59
    2ndf1
    wph
    @57
    @58
    @85
    cX
    wceq
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @33
    cB
    op2ndg
    syl2anc
    eqtrd
    #
    fveq12d
    eqtrd
    wph
    @78
    @0
    c1st
    cfv
    #
    cF
    wph
    @34
    cQ
    cO
    @12
    @0
    @35
    @38
    @39
    @42
    @63
    @47
    @44
    @55
    @59
    1stf1
    wph
    @57
    @58
    @87
    cF
    wceq
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @33
    cB
    op1stg
    syl2anc
    eqtrd
    opeq12d
    eqtrd
    wph
    @17
    @1
    @75
    cfv
    #
    @1
    @77
    cfv
    #
    cop
    @26
    wph
    @34
    @35
    @36
    @13
    cQ
    @11
    @12
    @38
    @1
    @43
    @42
    @63
    @54
    @56
    @62
    prf1
    wph
    @88
    @25
    @89
    cG
    wph
    @88
    @1
    @79
    cfv
    #
    @81
    cfv
    @25
    wph
    @34
    @35
    cO
    @36
    @10
    @9
    @1
    @42
    @49
    @53
    @62
    cofu1
    wph
    @90
    cP
    @81
    @6
    @84
    wph
    @90
    @1
    c2nd
    cfv
    #
    cP
    wph
    @34
    cQ
    cO
    @10
    @1
    @35
    @38
    @39
    @42
    @63
    @47
    @44
    @48
    @62
    2ndf1
    wph
    @60
    @61
    @91
    cP
    wceq
    yonedalem22.g
    yonedalem22.p
    cG
    cP
    @33
    cB
    op2ndg
    syl2anc
    eqtrd
    #
    fveq12d
    eqtrd
    wph
    @89
    @1
    c1st
    cfv
    #
    cG
    wph
    @34
    cQ
    cO
    @12
    @1
    @35
    @38
    @39
    @42
    @63
    @47
    @44
    @55
    @62
    1stf1
    wph
    @60
    @61
    @93
    cG
    wceq
    yonedalem22.g
    yonedalem22.p
    cG
    cP
    @33
    cB
    op1stg
    syl2anc
    eqtrd
    opeq12d
    eqtrd
    oveq12d
    wph
    @14
    @5
    @0
    @1
    @11
    c2nd
    cfv
    co
    cfv
    #
    @5
    @0
    @1
    @12
    c2nd
    cfv
    co
    #
    cfv
    #
    cop
    @74
    wph
    @34
    @35
    @36
    @13
    cQ
    @11
    @12
    @38
    @5
    @0
    @1
    @43
    @42
    @63
    @54
    @56
    @59
    @62
    @73
    prf2
    wph
    @94
    @22
    @96
    cA
    wph
    @94
    @5
    @0
    @1
    @10
    c2nd
    cfv
    co
    #
    cfv
    #
    @80
    @90
    @9
    c2nd
    cfv
    #
    co
    #
    cfv
    @22
    wph
    @34
    @35
    cO
    @5
    @36
    @10
    @9
    @38
    @0
    @1
    @42
    @49
    @53
    @59
    @62
    @63
    @73
    cofu2
    wph
    @98
    cK
    @100
    @21
    wph
    @100
    @90
    @80
    @7
    co
    #
    @21
    @100
    @80
    @90
    @8
    co
    @101
    @99
    @8
    @80
    @90
    @6
    @8
    @82
    @83
    op2nd
    oveqi
    @80
    @90
    @7
    ovtpos
    eqtri
    wph
    @90
    cP
    @80
    cX
    @7
    @92
    @86
    oveq12d
    syl5eq
    wph
    @98
    @5
    c2nd
    @69
    cres
    #
    cfv
    #
    @5
    c2nd
    cfv
    #
    cK
    wph
    @5
    @97
    @102
    wph
    @34
    cQ
    cO
    @10
    @0
    @1
    @35
    @38
    @39
    @42
    @63
    @47
    @44
    @48
    @59
    @62
    2ndf2
    fveq1d
    wph
    @5
    @69
    wcel
    #
    @103
    @104
    wceq
    @73
    @5
    @69
    c2nd
    fvres
    syl
    wph
    @70
    cK
    @72
    wcel
    #
    @104
    cK
    wceq
    yonedalem22.a
    yonedalem22.k
    cA
    cK
    @65
    @72
    op2ndg
    syl2anc
    3eqtrd
    fveq12d
    eqtrd
    wph
    @96
    @5
    c1st
    @69
    cres
    #
    cfv
    #
    @5
    c1st
    cfv
    #
    cA
    wph
    @5
    @95
    @107
    wph
    @34
    cQ
    cO
    @12
    @0
    @1
    @35
    @38
    @39
    @42
    @63
    @47
    @44
    @55
    @59
    @62
    1stf2
    fveq1d
    wph
    @105
    @108
    @109
    wceq
    @73
    @5
    @69
    c1st
    fvres
    syl
    wph
    @70
    @106
    @109
    cA
    wceq
    yonedalem22.a
    yonedalem22.k
    cA
    cK
    @65
    @72
    op1stg
    syl2anc
    3eqtrd
    opeq12d
    eqtrd
    fveq12d
    @22
    cA
    @27
    df-ov
    syl6eqr
    eqtrd
end
