include "cgrp.mm"
include "wcel.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cec.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "cuni.mm"
include "cxp.mm"
include "cin.mm"
include "cpco.mm"
include "comi.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cvv.mm"
include "eqid.mm"
include "pi1val.mm"
include "cbs.mm"
include "a1i.mm"
include "eqidd.mm"
include "pi1buni.mm"
include "fvexd.mm"
include "ovexd.mm"
include "cima.mm"
include "wss.mm"
include "cii.mm"
include "ccn.mm"
include "pi1blem.mm"
include "simpld.mm"
include "qusin.mm"
include "om1plusg.mm"
include "wer.mm"
include "phtpcer.mm"
include "simprd.mm"
include "erinxp.mm"
include "wbr.mm"
include "cplusg.mm"
include "pi1cpbl.mm"
include "oveqd.mm"
include "breq12d.mm"
include "sylibrd.mm"
include "w3a.mm"
include "ctopon.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "om1addcl.mm"
include "adantr.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "c4.mm"
include "cmul.mm"
include "caddc.mm"
include "cif.mm"
include "pi1eluni.mm"
include "biimpa.mm"
include "3ad2antr1.mm"
include "simp1d.mm"
include "mpbid.mm"
include "simp3d.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "pcoass.mm"
include "brinxp2.mm"
include "syl3anbrc.mm"
include "pcoptcl.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simpr.mm"
include "sselda.mm"
include "pcopt.mm"
include "pcorevcl.mm"
include "syl.mm"
include "eqtrd.mm"
include "wb.mm"
include "mpbir3and.mm"
include "csn.mm"
include "pcorev.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "syl6reqr.mm"
include "breqtrrd.mm"
include "qusgrp2.mm"
include "ecinxp.mm"
include "eqeq1d.mm"
include "anbi2d.mm"

theorem pi1grplem
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pi1fval.g: |- G = ( J pi1 Y )
  assume pi1fval.b: |- B = ( Base ` G )
  assume pi1fval.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1fval.4: |- ( ph -> Y e. X )
  assume pi1grplem.z: |- .0. = ( ( 0 [,] 1 ) X. { Y } )


  assert |- ( ph -> ( G e. Grp /\ [ .0. ] ( ~=ph ` J ) = ( 0g ` G ) ) )

  proof
    wph
    cG
    cgrp
    wcel
    #
    c.0
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    wa
    @0
    c.0
    @1
    cB
    cuni
    #
    @5
    cxp
    cin
    #
    cec
    #
    @3
    wceq
    #
    wa
    wph
    vx
    vy
    vz
    cJ
    cpco
    cfv
    #
    @6
    cJ
    cY
    comi
    co
    #
    cG
    va
    cc0
    c1
    cicc
    co
    #
    c1
    va
    cv
    #
    cmin
    co
    vx
    cv
    #
    cfv
    cmpt
    #
    @5
    cvv
    c.0
    vd
    vc
    va
    vb
    wph
    @1
    @10
    cG
    @5
    cvv
    cvv
    wph
    cG
    cJ
    @10
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @10
    eqid
    #
    pi1val
    wph
    cB
    cG
    cJ
    @10
    cbs
    cfv
    #
    @10
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @15
    cB
    cG
    cbs
    cfv
    wceq
    #
    wph
    pi1fval.b
    a1i
    #
    wph
    @16
    eqidd
    pi1buni
    #
    wph
    cJ
    cphtpc
    fvexd
    wph
    cJ
    cY
    comi
    ovexd
    #
    wph
    @1
    @5
    cima
    @5
    wss
    #
    @5
    cii
    cJ
    ccn
    co
    #
    wss
    #
    wph
    cB
    cG
    cJ
    @5
    @10
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @15
    @18
    @19
    pi1blem
    #
    simpld
    #
    qusin
    @19
    wph
    cJ
    @10
    cX
    cY
    @15
    pi1fval.3
    pi1fval.4
    om1plusg
    #
    wph
    @22
    @5
    @1
    @22
    @1
    wer
    wph
    cJ
    phtpcer
    a1i
    wph
    @21
    @23
    @24
    simprd
    #
    erinxp
    @20
    wph
    @12
    vc
    cv
    #
    @6
    wbr
    vb
    cv
    #
    vd
    cv
    #
    @6
    wbr
    wa
    @12
    @29
    @10
    cplusg
    cfv
    #
    co
    #
    @28
    @30
    @31
    co
    #
    @6
    wbr
    @12
    @29
    @9
    co
    #
    @28
    @30
    @9
    co
    #
    @6
    wbr
    wph
    cB
    @29
    @31
    @30
    @6
    cG
    cJ
    @12
    @28
    @10
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @18
    @6
    eqid
    @15
    @31
    eqid
    pi1cpbl
    wph
    @34
    @32
    @35
    @33
    @6
    wph
    @9
    @31
    @12
    @29
    @26
    oveqd
    wph
    @9
    @31
    @28
    @30
    @26
    oveqd
    breq12d
    sylibrd
    wph
    @13
    @5
    wcel
    #
    vy
    cv
    #
    @5
    wcel
    #
    w3a
    @5
    @13
    cJ
    @37
    @10
    cX
    cY
    @15
    wph
    @36
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @38
    pi1fval.3
    3ad2ant1
    wph
    @36
    cY
    cX
    wcel
    #
    @38
    pi1fval.4
    3ad2ant1
    wph
    @36
    @5
    @16
    wceq
    #
    @38
    @19
    3ad2ant1
    wph
    @36
    @38
    simp2
    wph
    @36
    @38
    simp3
    om1addcl
    #
    wph
    @36
    @38
    vz
    cv
    #
    @5
    wcel
    #
    w3a
    #
    wa
    #
    @13
    @37
    @9
    co
    #
    @43
    @9
    co
    #
    @5
    wcel
    @13
    @37
    @43
    @9
    co
    #
    @9
    co
    #
    @5
    wcel
    @48
    @50
    @1
    wbr
    @48
    @50
    @6
    wbr
    @46
    @5
    @47
    cJ
    @43
    @10
    cX
    cY
    @15
    wph
    @39
    @45
    pi1fval.3
    adantr
    #
    wph
    @40
    @45
    pi1fval.4
    adantr
    #
    wph
    @41
    @45
    @19
    adantr
    #
    wph
    @36
    @38
    @47
    @5
    wcel
    @44
    @42
    3adant3r3
    wph
    @36
    @38
    @44
    simpr3
    #
    om1addcl
    @46
    @5
    @13
    cJ
    @49
    @10
    cX
    cY
    @15
    @51
    @52
    @53
    wph
    @36
    @38
    @44
    simpr1
    @46
    @5
    @37
    cJ
    @43
    @10
    cX
    cY
    @15
    @51
    @52
    @53
    wph
    @36
    @38
    @44
    simpr2
    #
    @54
    om1addcl
    om1addcl
    @46
    vu
    vu
    @11
    vu
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    @56
    c1
    c4
    cdiv
    co
    #
    cle
    wbr
    c2
    @56
    cmul
    co
    @56
    @58
    caddc
    co
    cif
    @56
    c2
    cdiv
    co
    @57
    caddc
    co
    cif
    cmpt
    #
    @13
    @37
    @43
    cJ
    @46
    @13
    @22
    wcel
    #
    cc0
    @13
    cfv
    #
    cY
    wceq
    #
    c1
    @13
    cfv
    #
    cY
    wceq
    #
    wph
    @38
    @36
    @60
    @62
    @64
    w3a
    #
    @44
    wph
    @36
    @65
    wph
    cB
    @13
    cG
    cJ
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @18
    pi1eluni
    biimpa
    #
    3ad2antr1
    #
    simp1d
    @46
    @37
    @22
    wcel
    #
    cc0
    @37
    cfv
    #
    cY
    wceq
    #
    c1
    @37
    cfv
    #
    cY
    wceq
    #
    @46
    @38
    @68
    @70
    @72
    w3a
    @55
    @46
    cB
    @37
    cG
    cJ
    cX
    cY
    pi1fval.g
    @51
    @52
    @17
    @46
    pi1fval.b
    a1i
    #
    pi1eluni
    mpbid
    #
    simp1d
    @46
    @43
    @22
    wcel
    #
    cc0
    @43
    cfv
    #
    cY
    wceq
    #
    c1
    @43
    cfv
    cY
    wceq
    #
    @46
    @44
    @75
    @77
    @78
    w3a
    @54
    @46
    cB
    @43
    cG
    cJ
    cX
    cY
    pi1fval.g
    @51
    @52
    @73
    pi1eluni
    mpbid
    #
    simp1d
    @46
    @63
    cY
    @69
    @46
    @60
    @62
    @64
    @67
    simp3d
    @46
    @68
    @70
    @72
    @74
    simp2d
    eqtr4d
    @46
    @71
    cY
    @76
    @46
    @68
    @70
    @72
    @74
    simp3d
    @46
    @75
    @77
    @78
    @79
    simp2d
    eqtr4d
    @59
    eqid
    pcoass
    @48
    @50
    @5
    @5
    @1
    brinxp2
    syl3anbrc
    wph
    c.0
    @5
    wcel
    #
    c.0
    @22
    wcel
    cc0
    c.0
    cfv
    cY
    wceq
    c1
    c.0
    cfv
    cY
    wceq
    w3a
    #
    wph
    @39
    @40
    @81
    pi1fval.3
    pi1fval.4
    c.0
    cJ
    cX
    cY
    pi1grplem.z
    pcoptcl
    syl2anc
    wph
    cB
    c.0
    cG
    cJ
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @18
    pi1eluni
    mpbird
    #
    wph
    @36
    wa
    #
    c.0
    @13
    @9
    co
    #
    @5
    wcel
    @36
    @84
    @13
    @1
    wbr
    #
    @84
    @13
    @6
    wbr
    @83
    @5
    c.0
    cJ
    @13
    @10
    cX
    cY
    @15
    wph
    @39
    @36
    pi1fval.3
    adantr
    #
    wph
    @40
    @36
    pi1fval.4
    adantr
    #
    wph
    @41
    @36
    @19
    adantr
    #
    wph
    @80
    @36
    @82
    adantr
    #
    wph
    @36
    simpr
    #
    om1addcl
    @90
    @83
    @60
    @62
    @85
    wph
    @5
    @22
    @13
    @27
    sselda
    #
    @83
    @60
    @62
    @64
    @66
    simp2d
    #
    c.0
    @13
    cJ
    cY
    pi1grplem.z
    pcopt
    syl2anc
    @84
    @13
    @5
    @5
    @1
    brinxp2
    syl3anbrc
    @83
    @14
    @5
    wcel
    #
    @14
    @22
    wcel
    #
    cc0
    @14
    cfv
    #
    cY
    wceq
    #
    c1
    @14
    cfv
    #
    cY
    wceq
    #
    @83
    @94
    @95
    @63
    wceq
    #
    @97
    @61
    wceq
    #
    @83
    @60
    @94
    @99
    @100
    w3a
    @91
    va
    @13
    @14
    cJ
    @14
    eqid
    #
    pcorevcl
    syl
    #
    simp1d
    @83
    @95
    @63
    cY
    @83
    @94
    @99
    @100
    @102
    simp2d
    @83
    @60
    @62
    @64
    @66
    simp3d
    #
    eqtrd
    @83
    @97
    @61
    cY
    @83
    @94
    @99
    @100
    @102
    simp3d
    @92
    eqtrd
    wph
    @93
    @94
    @96
    @98
    w3a
    wb
    @36
    wph
    cB
    @14
    cG
    cJ
    cX
    cY
    pi1fval.g
    pi1fval.3
    pi1fval.4
    @18
    pi1eluni
    adantr
    mpbir3and
    #
    @83
    @14
    @13
    @9
    co
    #
    @5
    wcel
    @80
    @105
    c.0
    @1
    wbr
    @105
    c.0
    @6
    wbr
    @83
    @5
    @14
    cJ
    @13
    @10
    cX
    cY
    @15
    @86
    @87
    @88
    @104
    @90
    om1addcl
    @89
    @83
    @105
    @11
    @63
    csn
    #
    cxp
    #
    c.0
    @1
    @83
    @60
    @105
    @107
    @1
    wbr
    @91
    va
    @107
    @13
    @14
    cJ
    @101
    @107
    eqid
    pcorev
    syl
    @83
    @107
    @11
    cY
    csn
    #
    cxp
    c.0
    @83
    @106
    @108
    @11
    @83
    @63
    cY
    @103
    sneqd
    xpeq2d
    pi1grplem.z
    syl6reqr
    breqtrrd
    @105
    c.0
    @5
    @5
    @1
    brinxp2
    syl3anbrc
    qusgrp2
    wph
    @4
    @8
    @0
    wph
    @2
    @7
    @3
    wph
    @21
    @80
    @2
    @7
    wceq
    @25
    @82
    @5
    c.0
    @1
    ecinxp
    syl2anc
    eqeq1d
    anbi2d
    mpbird
end
