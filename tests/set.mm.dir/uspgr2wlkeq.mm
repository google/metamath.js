include "cuspgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wa.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "cfz.mm"
include "wb.mm"
include "3anan32.mm"
include "a1i.mm"
include "wlkeq.mm"
include "3expa.mm"
include "3adant1.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "ciedg.mm"
include "fzofzp1.mm"
include "adantl.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "wi.mm"
include "wss.mm"
include "fzossfz.mm"
include "ssralv.mm"
include "mp1i.mm"
include "r19.26.mm"
include "preq12.mm"
include "ralimdv.mm"
include "syl5bir.mm"
include "expd.mm"
include "syld.mm"
include "imp.mm"
include "mpd.mm"
include "ex.mm"
include "cdm.mm"
include "cword.mm"
include "cvtx.mm"
include "wf.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "eqid.mm"
include "upgrwlkcompim.mm"
include "syl.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "raleqdv.mm"
include "bi2anan9r.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "syl6bi.mm"
include "com13.mm"
include "ral2imi.mm"
include "sylbir.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "syl2and.mm"
include "3imp1.mm"
include "eqcom.mm"
include "crn.mm"
include "wf1.mm"
include "cedg.mm"
include "wf1o.mm"
include "uspgrf1oedg.mm"
include "f1of1.mm"
include "eqidd.mm"
include "edgval.mm"
include "eqcomi.mm"
include "f1eq123d.mm"
include "mpbird.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "wlkelwrd.mm"
include "eleq2d.mm"
include "wrdsymbcl.mm"
include "expcom.mm"
include "jcad.mm"
include "syl2an.mm"
include "f1veqaeq.mm"
include "syl2an2r.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "3syld.mm"
include "expimpd.mm"
include "pm4.71d.mm"
include "3bitr4d.mm"

theorem uspgr2wlkeq
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let vx: setvar x

  disjoint A y
  disjoint B y
  disjoint G y
  disjoint N y
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint G x
  disjoint N x
  assert |- ( ( G e. USPGraph /\ ( A e. ( Walks ` G ) /\ B e. ( Walks ` G ) ) /\ N = ( # ` ( 1st ` A ) ) ) -> ( A = B <-> ( N = ( # ` ( 1st ` B ) ) /\ A. y e. ( 0 ... N ) ( ( 2nd ` A ) ` y ) = ( ( 2nd ` B ) ` y ) ) ) )

  proof
    cG
    cuspgr
    wcel
    #
    cA
    cG
    cwlks
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cN
    cA
    c1st
    cfv
    #
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    cN
    cB
    c1st
    cfv
    #
    chash
    cfv
    #
    wceq
    #
    vy
    cv
    #
    @5
    cfv
    #
    @12
    @9
    cfv
    #
    wceq
    #
    vy
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    @12
    cA
    c2nd
    cfv
    #
    cfv
    #
    @12
    cB
    c2nd
    cfv
    #
    cfv
    #
    wceq
    #
    vy
    cc0
    cN
    cfz
    co
    #
    wral
    #
    w3a
    #
    @11
    @24
    wa
    #
    @17
    wa
    #
    cA
    cB
    wceq
    #
    @26
    @25
    @27
    wb
    @8
    @11
    @17
    @24
    3anan32
    a1i
    @4
    @7
    @28
    @25
    wb
    #
    @0
    @2
    @3
    @7
    @29
    vy
    cA
    cB
    cG
    cN
    wlkeq
    3expa
    3adant1
    @8
    @26
    @17
    @8
    @11
    @24
    @17
    @8
    @11
    wa
    #
    @24
    @19
    @12
    c1
    caddc
    co
    #
    @18
    cfv
    #
    cpr
    #
    @21
    @31
    @20
    cfv
    #
    cpr
    #
    wceq
    #
    vy
    @16
    wral
    #
    @14
    cG
    ciedg
    cfv
    #
    cfv
    #
    @13
    @38
    cfv
    #
    wceq
    #
    vy
    @16
    wral
    #
    @17
    @30
    @24
    @37
    @30
    @24
    wa
    #
    @32
    @34
    wceq
    #
    vy
    @16
    wral
    #
    @37
    @43
    vx
    cv
    #
    c1
    caddc
    co
    #
    @18
    cfv
    #
    @47
    @20
    cfv
    #
    wceq
    #
    vx
    @16
    wral
    @45
    @43
    @50
    vx
    @16
    @30
    @46
    @16
    wcel
    #
    @24
    @50
    @30
    @51
    wa
    #
    @22
    @50
    vy
    @47
    @23
    @51
    @47
    @23
    wcel
    @30
    cc0
    cN
    @46
    fzofzp1
    adantl
    @12
    @47
    wceq
    #
    @22
    @50
    wb
    @52
    @53
    @19
    @48
    @21
    @49
    @12
    @47
    @18
    fveq2
    @12
    @47
    @20
    fveq2
    eqeq12d
    adantl
    rspcdv
    impancom
    ralrimiv
    @44
    @50
    vy
    vx
    @16
    @12
    @46
    wceq
    #
    @32
    @48
    @34
    @49
    @54
    @31
    @47
    @18
    @12
    @46
    c1
    caddc
    oveq1
    #
    fveq2d
    @54
    @31
    @47
    @20
    @55
    fveq2d
    eqeq12d
    cbvralv
    sylibr
    @30
    @24
    @45
    @37
    wi
    #
    @30
    @24
    @22
    vy
    @16
    wral
    #
    @56
    @16
    @23
    wss
    @24
    @57
    wi
    @30
    cc0
    cN
    fzossfz
    @22
    vy
    @16
    @23
    ssralv
    mp1i
    @30
    @57
    @45
    @37
    @57
    @45
    wa
    @22
    @44
    wa
    #
    vy
    @16
    wral
    @30
    @37
    @22
    @44
    vy
    @16
    r19.26
    @30
    @58
    @36
    vy
    @16
    @58
    @36
    wi
    @30
    @19
    @32
    @21
    @34
    preq12
    a1i
    ralimdv
    syl5bir
    expd
    syld
    imp
    mpd
    ex
    @0
    @4
    @7
    @11
    @37
    @42
    wi
    #
    @0
    @2
    @5
    @38
    cdm
    #
    cword
    #
    wcel
    #
    cc0
    @6
    cfz
    co
    cG
    cvtx
    cfv
    #
    @18
    wf
    #
    @40
    @33
    wceq
    #
    vy
    cc0
    @6
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @3
    @9
    @61
    wcel
    #
    cc0
    @10
    cfz
    co
    @63
    @20
    wf
    #
    @39
    @35
    wceq
    #
    vy
    cc0
    @10
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @7
    @11
    @59
    wi
    wi
    #
    @0
    cG
    cupgr
    wcel
    #
    @2
    @68
    wi
    cG
    uspgrupgr
    #
    @76
    @2
    @68
    @18
    vy
    @5
    cG
    @38
    @63
    cA
    @63
    eqid
    #
    @38
    eqid
    #
    @5
    eqid
    #
    @18
    eqid
    #
    upgrwlkcompim
    ex
    syl
    @0
    @76
    @3
    @74
    wi
    @77
    @76
    @3
    @74
    @20
    vy
    @9
    cG
    @38
    @63
    cB
    @78
    @79
    @9
    eqid
    #
    @20
    eqid
    #
    upgrwlkcompim
    ex
    syl
    @68
    @74
    wa
    #
    @75
    wi
    @0
    @84
    @7
    @11
    @59
    @68
    @74
    @7
    @11
    wa
    #
    @59
    wi
    #
    @67
    @62
    @74
    @86
    wi
    @64
    @74
    @67
    @86
    @73
    @69
    @67
    @86
    wi
    @70
    @73
    @67
    @86
    @85
    @73
    @67
    wa
    #
    @59
    @85
    @87
    @71
    vy
    @16
    wral
    #
    @65
    vy
    @16
    wral
    #
    wa
    #
    @59
    @11
    @73
    @88
    @7
    @67
    @89
    @11
    @71
    vy
    @72
    @16
    @72
    @16
    wceq
    @10
    cN
    @10
    cN
    cc0
    cfzo
    oveq2
    eqcoms
    raleqdv
    @7
    @65
    vy
    @66
    @16
    @66
    @16
    wceq
    @6
    cN
    @6
    cN
    cc0
    cfzo
    oveq2
    eqcoms
    raleqdv
    bi2anan9r
    @90
    @71
    @65
    wa
    #
    vy
    @16
    wral
    @59
    @71
    @65
    vy
    @16
    r19.26
    @91
    @36
    @41
    vy
    @16
    @71
    @65
    @36
    @41
    wi
    @36
    @65
    @71
    @41
    @36
    @65
    @40
    @35
    wceq
    #
    @71
    @41
    wi
    @33
    @35
    @40
    eqeq2
    @92
    @71
    @41
    @71
    @41
    wb
    @35
    @40
    @35
    @40
    @39
    eqeq2
    eqcoms
    biimpd
    syl6bi
    com13
    imp
    ral2imi
    sylbir
    syl6bi
    com12
    ex
    3ad2ant3
    com12
    3ad2ant3
    imp
    expd
    a1i
    syl2and
    3imp1
    @30
    @41
    @15
    vy
    @16
    @41
    @40
    @39
    wceq
    #
    @30
    @12
    @16
    wcel
    #
    wa
    @15
    @39
    @40
    eqcom
    @30
    @60
    @38
    crn
    #
    @38
    wf1
    #
    @94
    @13
    @60
    wcel
    #
    @14
    @60
    wcel
    #
    wa
    #
    @93
    @15
    wi
    @8
    @96
    @11
    @0
    @4
    @96
    @7
    @0
    @96
    @60
    cG
    cedg
    cfv
    #
    @38
    wf1
    #
    @0
    @60
    @100
    @38
    wf1o
    @101
    @38
    cG
    @79
    uspgrf1oedg
    @60
    @100
    @38
    f1of1
    syl
    @0
    @60
    @60
    @95
    @100
    @38
    @38
    @0
    @38
    eqidd
    @0
    @60
    eqidd
    @95
    @100
    wceq
    @0
    @100
    @95
    cG
    edgval
    eqcomi
    a1i
    f1eq123d
    mpbird
    3ad2ant1
    adantr
    @30
    @94
    @99
    @8
    @11
    @94
    @99
    wi
    #
    @4
    @7
    @11
    @102
    wi
    #
    @0
    @4
    @7
    @103
    @4
    @7
    @11
    @102
    @4
    @85
    @94
    @99
    @2
    @62
    @64
    wa
    #
    @69
    @70
    wa
    #
    @85
    @94
    wa
    #
    @99
    wi
    #
    @3
    @18
    @5
    cG
    @38
    @63
    cA
    @78
    @79
    @80
    @81
    wlkelwrd
    @20
    @9
    cG
    @38
    @63
    cB
    @78
    @79
    @82
    @83
    wlkelwrd
    @104
    @105
    @107
    @62
    @105
    @107
    wi
    @64
    @105
    @62
    @107
    @69
    @62
    @107
    wi
    @70
    @69
    @62
    @107
    @69
    @62
    wa
    @106
    @97
    @98
    @62
    @106
    @97
    wi
    @69
    @106
    @62
    @97
    @85
    @94
    @62
    @97
    wi
    #
    @7
    @94
    @108
    wi
    @11
    @7
    @94
    @12
    @66
    wcel
    #
    @108
    @7
    @16
    @66
    @12
    cN
    @6
    cc0
    cfzo
    oveq2
    eleq2d
    @62
    @109
    @97
    @12
    @60
    @5
    wrdsymbcl
    expcom
    syl6bi
    adantr
    imp
    com12
    adantl
    @69
    @106
    @98
    wi
    @62
    @106
    @69
    @98
    @85
    @94
    @69
    @98
    wi
    #
    @11
    @94
    @110
    wi
    @7
    @11
    @94
    @12
    @72
    wcel
    #
    @110
    @11
    @16
    @72
    @12
    cN
    @10
    cc0
    cfzo
    oveq2
    eleq2d
    @69
    @111
    @98
    @12
    @60
    @9
    wrdsymbcl
    expcom
    syl6bi
    adantl
    imp
    com12
    adantr
    jcad
    ex
    adantr
    com12
    adantr
    imp
    syl2an
    expd
    expd
    imp
    3adant1
    imp
    imp
    @60
    @95
    @13
    @14
    @38
    f1veqaeq
    syl2an2r
    syl5bi
    ralimdva
    3syld
    expimpd
    pm4.71d
    3bitr4d
end
