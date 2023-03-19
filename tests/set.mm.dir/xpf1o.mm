include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "csb.mm"
include "c2nd.mm"
include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "cmpt2.mm"
include "wf1o.mm"
include "wa.mm"
include "xp1st.mm"
include "adantl.mm"
include "cmpt.mm"
include "eqid.mm"
include "f1ompt.mm"
include "sylib.mm"
include "simpld.mm"
include "adantr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "xp2nd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "weq.mm"
include "wb.mm"
include "wrex.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "reu6.mm"
include "anim12dan.mm"
include "reeanv.mm"
include "pm4.38.mm"
include "ex.mm"
include "ralimdv.mm"
include "com12.mm"
include "impcom.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl.mm"
include "vex.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "eqeq2d.mm"
include "op2ndd.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "ralxp.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfeq2.mm"
include "nfan.mm"
include "nfbi.mm"
include "nfral.mm"
include "anbi2d.mm"
include "opeq2.mm"
include "eqeq1d.mm"
include "cbvral.mm"
include "anbi1d.mm"
include "opeq1.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "bitr4i.mm"
include "eqeq2.mm"
include "opth.mm"
include "syl6bb.mm"
include "bibi2d.mm"
include "2ralbidv.mm"
include "rexxp.mm"
include "sylibr.mm"
include "ralrimivva.mm"
include "reubidv.mm"
include "nfop.mm"
include "opeq12.mm"
include "syl2an.mm"
include "cbvmpt2.mm"
include "opeq12d.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "sylanbrc.mm"

theorem xpf1o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume xpf1o.1: |- ( ph -> ( x e. A |-> X ) : A -1-1-onto-> B )
  assume xpf1o.2: |- ( ph -> ( y e. C |-> Y ) : C -1-1-onto-> D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint X y
  disjoint B x
  disjoint D y
  disjoint Y x
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C z
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint ph u
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( x e. A , y e. C |-> <. X , Y >. ) : ( A X. C ) -1-1-onto-> ( B X. D ) )

  proof
    wph
    vx
    vu
    cv
    #
    c1st
    cfv
    #
    cX
    csb
    #
    vy
    @0
    c2nd
    cfv
    #
    cY
    csb
    #
    cop
    #
    cB
    cD
    cxp
    #
    wcel
    #
    vu
    cA
    cC
    cxp
    #
    wral
    vv
    cv
    #
    @5
    wceq
    #
    vu
    @8
    wreu
    #
    vv
    @6
    wral
    #
    @8
    @6
    vx
    vy
    cA
    cC
    cX
    cY
    cop
    #
    cmpt2
    #
    wf1o
    wph
    @7
    vu
    @8
    wph
    @0
    @8
    wcel
    #
    wa
    #
    @2
    cB
    wcel
    #
    @4
    cD
    wcel
    #
    @7
    @16
    @1
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @17
    @15
    @19
    wph
    @0
    cA
    cC
    xp1st
    adantl
    wph
    @21
    @15
    wph
    @21
    vz
    cv
    #
    cX
    wceq
    #
    vx
    cA
    wreu
    #
    vz
    cB
    wral
    #
    wph
    cA
    cB
    vx
    cA
    cX
    cmpt
    #
    wf1o
    @21
    @25
    wa
    xpf1o.1
    vx
    vz
    cA
    cB
    cX
    @26
    @26
    eqid
    f1ompt
    sylib
    #
    simpld
    adantr
    @20
    @17
    vx
    @1
    cA
    vx
    @2
    cB
    vx
    @1
    cX
    nfcsb1v
    nfel1
    vx
    cv
    #
    @1
    wceq
    cX
    @2
    cB
    vx
    @1
    cX
    csbeq1a
    eleq1d
    rspc
    sylc
    @16
    @3
    cC
    wcel
    #
    cY
    cD
    wcel
    #
    vy
    cC
    wral
    #
    @18
    @15
    @29
    wph
    @0
    cA
    cC
    xp2nd
    adantl
    wph
    @31
    @15
    wph
    @31
    vw
    cv
    #
    cY
    wceq
    #
    vy
    cC
    wreu
    #
    vw
    cD
    wral
    #
    wph
    cC
    cD
    vy
    cC
    cY
    cmpt
    #
    wf1o
    @31
    @35
    wa
    xpf1o.2
    vy
    vw
    cC
    cD
    cY
    @36
    @36
    eqid
    f1ompt
    sylib
    #
    simpld
    adantr
    @30
    @18
    vy
    @3
    cC
    vy
    @4
    cD
    vy
    @3
    cY
    nfcsb1v
    nfel1
    vy
    cv
    #
    @3
    wceq
    cY
    @4
    cD
    vy
    @3
    cY
    csbeq1a
    eleq1d
    rspc
    sylc
    @2
    @4
    cB
    cD
    opelxpi
    syl2anc
    ralrimiva
    wph
    @22
    @2
    wceq
    #
    @32
    @4
    wceq
    #
    wa
    #
    vu
    @8
    wreu
    #
    vw
    cD
    wral
    vz
    cB
    wral
    @12
    wph
    @42
    vz
    vw
    cB
    cD
    wph
    @22
    cB
    wcel
    #
    @32
    cD
    wcel
    #
    wa
    wa
    #
    @41
    vu
    vv
    weq
    #
    wb
    #
    vu
    @8
    wral
    #
    vv
    @8
    wrex
    #
    @42
    @45
    @23
    @33
    wa
    #
    vx
    vs
    weq
    #
    vy
    vt
    weq
    #
    wa
    #
    wb
    #
    vy
    cC
    wral
    #
    vx
    cA
    wral
    #
    vt
    cC
    wrex
    #
    vs
    cA
    wrex
    #
    @49
    @45
    @23
    @51
    wb
    #
    vx
    cA
    wral
    #
    vs
    cA
    wrex
    #
    @33
    @52
    wb
    #
    vy
    cC
    wral
    #
    vt
    cC
    wrex
    #
    wa
    #
    @58
    wph
    @43
    @61
    @44
    @64
    wph
    @43
    wa
    @24
    @61
    wph
    @24
    vz
    cB
    wph
    @21
    @25
    @27
    simprd
    r19.21bi
    @23
    vx
    vs
    cA
    reu6
    sylib
    wph
    @44
    wa
    @34
    @64
    wph
    @34
    vw
    cD
    wph
    @31
    @35
    @37
    simprd
    r19.21bi
    @33
    vy
    vt
    cC
    reu6
    sylib
    anim12dan
    @65
    @60
    @63
    wa
    #
    vt
    cC
    wrex
    #
    vs
    cA
    wrex
    @58
    @60
    @63
    vs
    vt
    cA
    cC
    reeanv
    @67
    @57
    vs
    cA
    @66
    @56
    vt
    cC
    @63
    @60
    @56
    @63
    @59
    @55
    vx
    cA
    @59
    @63
    @55
    @59
    @62
    @54
    vy
    cC
    @59
    @62
    @54
    @23
    @33
    @51
    @52
    pm4.38
    ex
    ralimdv
    com12
    ralimdv
    impcom
    reximi
    reximi
    sylbir
    syl
    @48
    @56
    vv
    vs
    vt
    cA
    cC
    @48
    @50
    @28
    @38
    cop
    #
    @9
    wceq
    #
    wb
    #
    vy
    cC
    wral
    #
    vx
    cA
    wral
    #
    @9
    vs
    cv
    #
    vt
    cv
    #
    cop
    #
    wceq
    #
    @56
    @48
    @22
    vx
    @73
    cX
    csb
    #
    wceq
    #
    @32
    vy
    @74
    cY
    csb
    #
    wceq
    #
    wa
    #
    @75
    @9
    wceq
    #
    wb
    #
    vt
    cC
    wral
    #
    vs
    cA
    wral
    @72
    @47
    @83
    vu
    vs
    vt
    cA
    cC
    @0
    @75
    wceq
    #
    @41
    @81
    @46
    @82
    @85
    @39
    @78
    @40
    @80
    @85
    @2
    @77
    @22
    @85
    vx
    @1
    @73
    cX
    @73
    @74
    @0
    vs
    vex
    #
    vt
    vex
    #
    op1std
    csbeq1d
    eqeq2d
    @85
    @4
    @79
    @32
    @85
    vy
    @3
    @74
    cY
    @73
    @74
    @0
    @86
    @87
    op2ndd
    csbeq1d
    eqeq2d
    anbi12d
    @0
    @75
    @9
    eqeq1
    bibi12d
    ralxp
    @71
    @84
    vx
    vs
    cA
    @71
    vs
    nfv
    @83
    vx
    vt
    cC
    vx
    cC
    nfcv
    @81
    @82
    vx
    @78
    @80
    vx
    vx
    @22
    @77
    vx
    @73
    cX
    nfcsb1v
    nfeq2
    @80
    vx
    nfv
    nfan
    @82
    vx
    nfv
    nfbi
    nfral
    @71
    @23
    @80
    wa
    #
    @28
    @74
    cop
    #
    @9
    wceq
    #
    wb
    #
    vt
    cC
    wral
    @51
    @84
    @70
    @91
    vy
    vt
    cC
    @70
    vt
    nfv
    @88
    @90
    vy
    @23
    @80
    vy
    @23
    vy
    nfv
    vy
    @32
    @79
    vy
    @74
    cY
    nfcsb1v
    nfeq2
    nfan
    @90
    vy
    nfv
    nfbi
    @52
    @50
    @88
    @69
    @90
    @52
    @33
    @80
    @23
    @52
    cY
    @79
    @32
    vy
    @74
    cY
    csbeq1a
    eqeq2d
    anbi2d
    @52
    @68
    @89
    @9
    @38
    @74
    @28
    opeq2
    eqeq1d
    bibi12d
    cbvral
    @51
    @91
    @83
    vt
    cC
    @51
    @88
    @81
    @90
    @82
    @51
    @23
    @78
    @80
    @51
    cX
    @77
    @22
    vx
    @73
    cX
    csbeq1a
    eqeq2d
    anbi1d
    @51
    @89
    @75
    @9
    @28
    @73
    @74
    opeq1
    eqeq1d
    bibi12d
    ralbidv
    syl5bb
    cbvral
    bitr4i
    @76
    @70
    @54
    vx
    vy
    cA
    cC
    @76
    @69
    @53
    @50
    @76
    @69
    @68
    @75
    wceq
    @53
    @9
    @75
    @68
    eqeq2
    @28
    @38
    @73
    @74
    vx
    vex
    vy
    vex
    opth
    syl6bb
    bibi2d
    2ralbidv
    syl5bb
    rexxp
    sylibr
    @41
    vu
    vv
    @8
    reu6
    sylibr
    ralrimivva
    @11
    @42
    vv
    vz
    vw
    cB
    cD
    @9
    @22
    @32
    cop
    #
    wceq
    #
    @10
    @41
    vu
    @8
    @93
    @10
    @92
    @5
    wceq
    @41
    @9
    @92
    @5
    eqeq1
    @22
    @32
    @2
    @4
    vz
    vex
    #
    vw
    vex
    #
    opth
    syl6bb
    reubidv
    ralxp
    sylibr
    vu
    vv
    @8
    @6
    @5
    @14
    @14
    vz
    vw
    cA
    cC
    vx
    @22
    cX
    csb
    #
    vy
    @32
    cY
    csb
    #
    cop
    #
    cmpt2
    vu
    @8
    @5
    cmpt
    vx
    vy
    vz
    vw
    cA
    cC
    @13
    @98
    vz
    @13
    nfcv
    vw
    @13
    nfcv
    vx
    @96
    @97
    vx
    @22
    cX
    nfcsb1v
    vx
    @97
    nfcv
    nfop
    vy
    @96
    @97
    vy
    @96
    nfcv
    vy
    @32
    cY
    nfcsb1v
    nfop
    vx
    vz
    weq
    cX
    @96
    wceq
    cY
    @97
    wceq
    @13
    @98
    wceq
    vy
    vw
    weq
    vx
    @22
    cX
    csbeq1a
    vy
    @32
    cY
    csbeq1a
    cX
    cY
    @96
    @97
    opeq12
    syl2an
    cbvmpt2
    vz
    vw
    vu
    cA
    cC
    @5
    @98
    @0
    @92
    wceq
    #
    @2
    @96
    @4
    @97
    @99
    vx
    @1
    @22
    cX
    @22
    @32
    @0
    @94
    @95
    op1std
    csbeq1d
    @99
    vy
    @3
    @32
    cY
    @22
    @32
    @0
    @94
    @95
    op2ndd
    csbeq1d
    opeq12d
    mpt2mpt
    eqtr4i
    f1ompt
    sylanbrc
end
