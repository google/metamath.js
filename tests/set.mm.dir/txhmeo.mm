include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "ccnv.mm"
include "chmeo.mm"
include "ctop.mm"
include "ctopon.mm"
include "hmeocn.mm"
include "syl.mm"
include "cntop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnmpt1st.mm"
include "cnmpt21f.mm"
include "cnmpt2nd.mm"
include "cnmpt2t.mm"
include "cuni.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "opeq12d.mm"
include "mpt2mpt.mm"
include "eqcomi.mm"
include "wa.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "xp1st.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "xp2nd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "hmeof1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "wb.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "f1ocnvfvb.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "anbi12d.mm"
include "eqop.mm"
include "3bitr4rd.mm"
include "f1ocnv2d.mm"
include "simprd.mm"
include "syl6eq.mm"
include "cntop2.mm"
include "hmeocnvcn.mm"
include "eqeltrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem txhmeo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume txhmeo.1: |- X = U. J
  assume txhmeo.2: |- Y = U. K
  assume txhmeo.3: |- ( ph -> F e. ( J Homeo L ) )
  assume txhmeo.4: |- ( ph -> G e. ( K Homeo M ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  disjoint L x
  disjoint L y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint M x
  disjoint M y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint J w
  disjoint J z
  disjoint K w
  disjoint K z
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G z
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L z
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M z
  assert |- ( ph -> ( x e. X , y e. Y |-> <. ( F ` x ) , ( G ` y ) >. ) e. ( ( J tX K ) Homeo ( L tX M ) ) )

  proof
    wph
    vx
    vy
    cX
    cY
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
    #
    cJ
    cK
    ctx
    co
    #
    cL
    cM
    ctx
    co
    #
    ccn
    co
    wcel
    @5
    ccnv
    #
    @7
    @6
    ccn
    co
    #
    wcel
    @5
    @6
    @7
    chmeo
    co
    wcel
    wph
    vx
    vy
    @1
    @3
    cJ
    cK
    cL
    cM
    cX
    cY
    wph
    cJ
    ctop
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    wph
    cF
    cJ
    cL
    ccn
    co
    wcel
    #
    @10
    wph
    cF
    cJ
    cL
    chmeo
    co
    wcel
    #
    @11
    txhmeo.3
    cF
    cJ
    cL
    hmeocn
    syl
    #
    cF
    cJ
    cL
    cntop1
    syl
    cJ
    cX
    txhmeo.1
    toptopon
    sylib
    #
    wph
    cK
    ctop
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    wph
    cG
    cK
    cM
    ccn
    co
    wcel
    #
    @15
    wph
    cG
    cK
    cM
    chmeo
    co
    wcel
    #
    @16
    txhmeo.4
    cG
    cK
    cM
    hmeocn
    syl
    #
    cG
    cK
    cM
    cntop1
    syl
    cK
    cY
    txhmeo.2
    toptopon
    sylib
    #
    wph
    vx
    vy
    @0
    cF
    cJ
    cK
    cJ
    cL
    cX
    cY
    @14
    @19
    wph
    vx
    vy
    cJ
    cK
    cX
    cY
    @14
    @19
    cnmpt1st
    @13
    cnmpt21f
    wph
    vx
    vy
    @2
    cG
    cJ
    cK
    cK
    cM
    cX
    cY
    @14
    @19
    wph
    vx
    vy
    cJ
    cK
    cX
    cY
    @14
    @19
    cnmpt2nd
    @18
    cnmpt21f
    cnmpt2t
    wph
    @8
    vz
    vw
    cL
    cuni
    #
    cM
    cuni
    #
    vz
    cv
    #
    cF
    ccnv
    #
    cfv
    #
    vw
    cv
    #
    cG
    ccnv
    #
    cfv
    #
    cop
    #
    cmpt2
    #
    @9
    wph
    @8
    vv
    @20
    @21
    cxp
    #
    vv
    cv
    #
    c1st
    cfv
    #
    @23
    cfv
    #
    @31
    c2nd
    cfv
    #
    @26
    cfv
    #
    cop
    #
    cmpt
    #
    @29
    wph
    cX
    cY
    cxp
    #
    @30
    @5
    wf1o
    @8
    @37
    wceq
    wph
    vu
    vv
    @38
    @30
    vu
    cv
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @39
    c2nd
    cfv
    #
    cG
    cfv
    #
    cop
    #
    @36
    @5
    vu
    @38
    @44
    cmpt
    @5
    vx
    vy
    vu
    cX
    cY
    @44
    @4
    @39
    @0
    @2
    cop
    wceq
    #
    @41
    @1
    @43
    @3
    @45
    @40
    @0
    cF
    @0
    @2
    @39
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    @45
    @42
    @2
    cG
    @0
    @2
    @39
    @46
    @47
    op2ndd
    fveq2d
    opeq12d
    mpt2mpt
    eqcomi
    wph
    @39
    @38
    wcel
    #
    wa
    @41
    @20
    wcel
    #
    @43
    @21
    wcel
    #
    @44
    @30
    wcel
    wph
    cX
    @20
    cF
    wf
    #
    @40
    cX
    wcel
    #
    @49
    @48
    wph
    @11
    @51
    @13
    cF
    cJ
    cL
    cX
    @20
    txhmeo.1
    @20
    eqid
    #
    cnf
    syl
    @39
    cX
    cY
    xp1st
    #
    cX
    @20
    @40
    cF
    ffvelrn
    syl2an
    wph
    cY
    @21
    cG
    wf
    #
    @42
    cY
    wcel
    #
    @50
    @48
    wph
    @16
    @55
    @18
    cG
    cK
    cM
    cY
    @21
    txhmeo.2
    @21
    eqid
    #
    cnf
    syl
    @39
    cX
    cY
    xp2nd
    #
    cY
    @21
    @42
    cG
    ffvelrn
    syl2an
    @41
    @43
    @20
    @21
    opelxpi
    syl2anc
    wph
    @31
    @30
    wcel
    #
    wa
    @33
    cX
    wcel
    #
    @35
    cY
    wcel
    #
    @36
    @38
    wcel
    wph
    @20
    cX
    @23
    wf
    #
    @32
    @20
    wcel
    #
    @60
    @59
    wph
    cX
    @20
    cF
    wf1o
    #
    @20
    cX
    @23
    wf1o
    @62
    wph
    @12
    @64
    txhmeo.3
    cF
    cJ
    cL
    cX
    @20
    txhmeo.1
    @53
    hmeof1o
    syl
    #
    cX
    @20
    cF
    f1ocnv
    @20
    cX
    @23
    f1of
    3syl
    @31
    @20
    @21
    xp1st
    #
    @20
    cX
    @32
    @23
    ffvelrn
    syl2an
    wph
    @21
    cY
    @26
    wf
    #
    @34
    @21
    wcel
    #
    @61
    @59
    wph
    cY
    @21
    cG
    wf1o
    #
    @21
    cY
    @26
    wf1o
    @67
    wph
    @17
    @69
    txhmeo.4
    cG
    cK
    cM
    cY
    @21
    txhmeo.2
    @57
    hmeof1o
    syl
    #
    cY
    @21
    cG
    f1ocnv
    @21
    cY
    @26
    f1of
    3syl
    @31
    @20
    @21
    xp2nd
    #
    @21
    cY
    @34
    @26
    ffvelrn
    syl2an
    @33
    @35
    cX
    cY
    opelxpi
    syl2anc
    wph
    @48
    @59
    wa
    #
    wa
    #
    @32
    @41
    wceq
    #
    @34
    @43
    wceq
    #
    wa
    #
    @40
    @33
    wceq
    #
    @42
    @35
    wceq
    #
    wa
    #
    @31
    @44
    wceq
    #
    @39
    @36
    wceq
    #
    @73
    @74
    @77
    @75
    @78
    @73
    @41
    @32
    wceq
    #
    @33
    @40
    wceq
    #
    @74
    @77
    @73
    @64
    @52
    @63
    @82
    @83
    wb
    wph
    @64
    @72
    @65
    adantr
    @48
    @52
    wph
    @59
    @54
    ad2antrl
    @59
    @63
    wph
    @48
    @66
    ad2antll
    cX
    @20
    @40
    @32
    cF
    f1ocnvfvb
    syl3anc
    @32
    @41
    eqcom
    @40
    @33
    eqcom
    3bitr4g
    @73
    @43
    @34
    wceq
    #
    @35
    @42
    wceq
    #
    @75
    @78
    @73
    @69
    @56
    @68
    @84
    @85
    wb
    wph
    @69
    @72
    @70
    adantr
    @48
    @56
    wph
    @59
    @58
    ad2antrl
    @59
    @68
    wph
    @48
    @71
    ad2antll
    cY
    @21
    @42
    @34
    cG
    f1ocnvfvb
    syl3anc
    @34
    @43
    eqcom
    @42
    @35
    eqcom
    3bitr4g
    anbi12d
    @59
    @80
    @76
    wb
    wph
    @48
    @31
    @41
    @43
    @20
    @21
    eqop
    ad2antll
    @48
    @81
    @79
    wb
    wph
    @59
    @39
    @33
    @35
    cX
    cY
    eqop
    ad2antrl
    3bitr4rd
    f1ocnv2d
    simprd
    vz
    vw
    vv
    @20
    @21
    @36
    @28
    @31
    @22
    @25
    cop
    wceq
    #
    @33
    @24
    @35
    @27
    @86
    @32
    @22
    @23
    @22
    @25
    @31
    vz
    vex
    #
    vw
    vex
    #
    op1std
    fveq2d
    @86
    @34
    @25
    @26
    @22
    @25
    @31
    @87
    @88
    op2ndd
    fveq2d
    opeq12d
    mpt2mpt
    syl6eq
    wph
    vz
    vw
    @24
    @27
    cL
    cM
    cJ
    cK
    @20
    @21
    wph
    cL
    ctop
    wcel
    #
    cL
    @20
    ctopon
    cfv
    wcel
    wph
    @11
    @89
    @13
    cF
    cJ
    cL
    cntop2
    syl
    cL
    @20
    @53
    toptopon
    sylib
    #
    wph
    cM
    ctop
    wcel
    #
    cM
    @21
    ctopon
    cfv
    wcel
    wph
    @16
    @91
    @18
    cG
    cK
    cM
    cntop2
    syl
    cM
    @21
    @57
    toptopon
    sylib
    #
    wph
    vz
    vw
    @22
    @23
    cL
    cM
    cL
    cJ
    @20
    @21
    @90
    @92
    wph
    vz
    vw
    cL
    cM
    @20
    @21
    @90
    @92
    cnmpt1st
    wph
    @12
    @23
    cL
    cJ
    ccn
    co
    wcel
    txhmeo.3
    cF
    cJ
    cL
    hmeocnvcn
    syl
    cnmpt21f
    wph
    vz
    vw
    @25
    @26
    cL
    cM
    cM
    cK
    @20
    @21
    @90
    @92
    wph
    vz
    vw
    cL
    cM
    @20
    @21
    @90
    @92
    cnmpt2nd
    wph
    @17
    @26
    cM
    cK
    ccn
    co
    wcel
    txhmeo.4
    cG
    cK
    cM
    hmeocnvcn
    syl
    cnmpt21f
    cnmpt2t
    eqeltrd
    @5
    @6
    @7
    ishmeo
    sylanbrc
end
