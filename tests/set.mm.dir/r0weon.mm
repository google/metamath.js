include "con0.mm"
include "cxp.mm"
include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wtru.mm"
include "cep.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cun.mm"
include "cmpt.mm"
include "wcel.mm"
include "wceq.mm"
include "wbr.mm"
include "wo.mm"
include "copab.mm"
include "weq.mm"
include "fveq2.mm"
include "uneq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "unex.mm"
include "fvmpt.mm"
include "breqan12d.mm"
include "epelc.mm"
include "syl6bb.mm"
include "eqeqan12d.mm"
include "anbi1d.mm"
include "orbi12d.mm"
include "pm5.32i.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "wf.mm"
include "word.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "elon.mm"
include "ordun.mm"
include "syl2anb.mm"
include "syl2anc.mm"
include "sylibr.mm"
include "fmpti.mm"
include "a1i.mm"
include "epweon.mm"
include "leweon.mm"
include "cima.mm"
include "cvv.mm"
include "cdm.mm"
include "crn.mm"
include "vex.mm"
include "dmex.mm"
include "rnex.mm"
include "cres.mm"
include "imadmres.mm"
include "wss.mm"
include "ccnv.mm"
include "cin.mm"
include "crab.mm"
include "wral.mm"
include "inss2.mm"
include "cpr.mm"
include "ssun1.mm"
include "cop.mm"
include "sseli.mm"
include "1st2nd2.mm"
include "syl.mm"
include "inss1.mm"
include "eqeltrrd.mm"
include "opeldm.mm"
include "sseldi.mm"
include "ssun2.mm"
include "opelrn.mm"
include "prssi.mm"
include "ordunpr.mm"
include "sseldd.mm"
include "rgen.mm"
include "ssrab.mm"
include "mpbir2an.mm"
include "dmres.mm"
include "fdmi.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "mptpreima.mm"
include "3sstr4i.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt.mm"
include "resss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "funimass3.mm"
include "mp2an.mm"
include "mpbir.mm"
include "eqsstr3i.mm"
include "ssexi.mm"
include "fnwe.mm"
include "epse.mm"
include "cuni.mm"
include "cpw.mm"
include "vuniex.mm"
include "pwex.mm"
include "xpex.mm"
include "cab.mm"
include "df-rab.mm"
include "adantr.mm"
include "elssuni.mm"
include "adantl.mm"
include "unssad.mm"
include "elpw.mm"
include "unssbd.mm"
include "jca.mm"
include "elxp6.mm"
include "sylanbrc.mm"
include "abssi.mm"
include "eqsstri.mm"
include "fnse.mm"
include "trud.mm"

theorem r0weon
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cR: class R
  let cL: class L
  let cA: class A
  let va: setvar a
  let cJ: class J
  let vu: setvar u
  let vm: setvar m
  let cM: class M
  let wph: wff ph
  let cQ: class Q
  assume leweon.1: |- L = { <. x , y >. | ( ( x e. ( On X. On ) /\ y e. ( On X. On ) ) /\ ( ( 1st ` x ) e. ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) e. ( 2nd ` y ) ) ) ) }
  assume r0weon.1: |- R = { <. z , w >. | ( ( z e. ( On X. On ) /\ w e. ( On X. On ) ) /\ ( ( ( 1st ` z ) u. ( 2nd ` z ) ) e. ( ( 1st ` w ) u. ( 2nd ` w ) ) \/ ( ( ( 1st ` z ) u. ( 2nd ` z ) ) = ( ( 1st ` w ) u. ( 2nd ` w ) ) /\ z L w ) ) ) }

  disjoint w z
  disjoint L w
  disjoint L z
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint J w
  disjoint u w
  disjoint u z
  disjoint L u
  disjoint m z
  disjoint M m
  disjoint M z
  disjoint ph w
  disjoint ph z
  disjoint Q z
  disjoint a m
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint u x
  disjoint u y
  disjoint R u
  assert |- ( R We ( On X. On ) /\ R Se ( On X. On ) )

  proof
    con0
    con0
    cxp
    #
    cR
    wwe
    #
    @0
    cR
    wse
    #
    wa
    wtru
    @1
    @2
    wtru
    vz
    vw
    vu
    @0
    con0
    cep
    cL
    cR
    vx
    @0
    vx
    cv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cun
    #
    cmpt
    #
    cR
    vz
    cv
    #
    @0
    wcel
    #
    vw
    cv
    #
    @0
    wcel
    #
    wa
    #
    @8
    c1st
    cfv
    #
    @8
    c2nd
    cfv
    #
    cun
    #
    @10
    c1st
    cfv
    #
    @10
    c2nd
    cfv
    #
    cun
    #
    wcel
    #
    @15
    @18
    wceq
    #
    @8
    @10
    cL
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    vz
    vw
    copab
    @12
    @8
    @7
    cfv
    #
    @10
    @7
    cfv
    #
    cep
    wbr
    #
    @25
    @26
    wceq
    #
    @21
    wa
    #
    wo
    #
    wa
    #
    vz
    vw
    copab
    r0weon.1
    @31
    @24
    vz
    vw
    @12
    @30
    @23
    @12
    @27
    @19
    @29
    @22
    @12
    @27
    @15
    @18
    cep
    wbr
    @19
    @9
    @11
    @25
    @15
    @26
    @18
    cep
    vx
    @8
    @6
    @15
    @0
    @7
    vx
    vz
    weq
    @4
    @13
    @5
    @14
    @3
    @8
    c1st
    fveq2
    @3
    @8
    c2nd
    fveq2
    uneq12d
    @7
    eqid
    #
    @13
    @14
    @8
    c1st
    fvex
    @8
    c2nd
    fvex
    unex
    fvmpt
    #
    vx
    @10
    @6
    @18
    @0
    @7
    vx
    vw
    weq
    @4
    @16
    @5
    @17
    @3
    @10
    c1st
    fveq2
    @3
    @10
    c2nd
    fveq2
    uneq12d
    @32
    @16
    @17
    @10
    c1st
    fvex
    @10
    c2nd
    fvex
    unex
    #
    fvmpt
    #
    breqan12d
    @15
    @18
    @34
    epelc
    syl6bb
    @12
    @28
    @20
    @21
    @9
    @11
    @25
    @15
    @26
    @18
    @33
    @35
    eqeqan12d
    anbi1d
    orbi12d
    pm5.32i
    opabbii
    eqtr4i
    #
    @0
    con0
    @7
    wf
    wtru
    vx
    @0
    con0
    @6
    @7
    @32
    @3
    @0
    wcel
    #
    @6
    word
    #
    @6
    con0
    wcel
    @37
    @4
    con0
    wcel
    #
    @5
    con0
    wcel
    #
    @38
    @3
    con0
    con0
    xp1st
    #
    @3
    con0
    con0
    xp2nd
    #
    @39
    @4
    word
    @5
    word
    @38
    @40
    @4
    @3
    c1st
    fvex
    #
    elon
    @5
    @3
    c2nd
    fvex
    #
    elon
    @4
    @5
    ordun
    syl2anb
    syl2anc
    @6
    @4
    @5
    @43
    @44
    unex
    elon
    sylibr
    fmpti
    #
    a1i
    #
    con0
    cep
    wwe
    wtru
    epweon
    a1i
    @0
    cL
    wwe
    wtru
    vx
    vy
    cL
    leweon.1
    leweon
    a1i
    @7
    vu
    cv
    #
    cima
    #
    cvv
    wcel
    wtru
    @48
    @47
    cdm
    #
    @47
    crn
    #
    cun
    #
    @49
    @50
    @47
    vu
    vex
    #
    dmex
    @47
    @52
    rnex
    unex
    @48
    @7
    @7
    @47
    cres
    #
    cdm
    #
    cima
    #
    @51
    @7
    @47
    imadmres
    @55
    @51
    wss
    #
    @54
    @7
    ccnv
    #
    @51
    cima
    #
    wss
    #
    @47
    @0
    cin
    #
    @6
    @51
    wcel
    #
    vx
    @0
    crab
    #
    @54
    @58
    @60
    @62
    wss
    @60
    @0
    wss
    @61
    vx
    @60
    wral
    @47
    @0
    inss2
    #
    @61
    vx
    @60
    @3
    @60
    wcel
    #
    @4
    @5
    cpr
    #
    @51
    @6
    @64
    @4
    @51
    wcel
    @5
    @51
    wcel
    @65
    @51
    wss
    @64
    @49
    @51
    @4
    @49
    @50
    ssun1
    @64
    @4
    @5
    cop
    #
    @47
    wcel
    #
    @4
    @49
    wcel
    @64
    @3
    @66
    @47
    @64
    @37
    @3
    @66
    wceq
    #
    @60
    @0
    @3
    @63
    sseli
    #
    @3
    con0
    con0
    1st2nd2
    #
    syl
    @60
    @47
    @3
    @47
    @0
    inss1
    sseli
    eqeltrrd
    #
    @4
    @5
    @47
    @43
    @44
    opeldm
    syl
    sseldi
    @64
    @50
    @51
    @5
    @50
    @49
    ssun2
    @64
    @67
    @5
    @50
    wcel
    @71
    @4
    @5
    @47
    @43
    @44
    opelrn
    syl
    sseldi
    @4
    @5
    @51
    prssi
    syl2anc
    @64
    @39
    @40
    @6
    @65
    wcel
    @64
    @37
    @39
    @69
    @41
    syl
    @64
    @37
    @40
    @69
    @42
    syl
    @4
    @5
    ordunpr
    syl2anc
    sseldd
    rgen
    @61
    vx
    @0
    @60
    ssrab
    mpbir2an
    @54
    @47
    @7
    cdm
    #
    cin
    @60
    @7
    @47
    dmres
    @72
    @0
    @47
    @0
    con0
    @7
    @45
    fdmi
    ineq2i
    eqtri
    vx
    @0
    @6
    @51
    @7
    @32
    mptpreima
    3sstr4i
    @7
    wfun
    @54
    @72
    wss
    #
    @56
    @59
    wb
    vx
    @0
    @6
    funmpt
    @53
    @7
    wss
    @73
    @7
    @47
    resss
    @53
    @7
    dmss
    ax-mp
    @54
    @51
    @7
    funimass3
    mp2an
    mpbir
    eqsstr3i
    ssexi
    a1i
    fnwe
    wtru
    vz
    vw
    vu
    @0
    con0
    cep
    cL
    cR
    @7
    @36
    @46
    con0
    cep
    wse
    wtru
    con0
    epse
    a1i
    @57
    @47
    cima
    #
    cvv
    wcel
    wtru
    @74
    @47
    cuni
    #
    cpw
    #
    @76
    cxp
    #
    @76
    @76
    @75
    vu
    vuniex
    pwex
    #
    @78
    xpex
    @74
    @37
    @6
    @47
    wcel
    #
    wa
    #
    vx
    cab
    #
    @77
    @74
    @79
    vx
    @0
    crab
    @81
    vx
    @0
    @6
    @47
    @7
    @32
    mptpreima
    @79
    vx
    @0
    df-rab
    eqtri
    @80
    vx
    @77
    @80
    @68
    @4
    @76
    wcel
    #
    @5
    @76
    wcel
    #
    wa
    @3
    @77
    wcel
    @37
    @68
    @79
    @70
    adantr
    @80
    @82
    @83
    @80
    @4
    @75
    wss
    @82
    @80
    @4
    @5
    @75
    @79
    @6
    @75
    wss
    @37
    @6
    @47
    elssuni
    adantl
    #
    unssad
    @4
    @75
    @43
    elpw
    sylibr
    @80
    @5
    @75
    wss
    @83
    @80
    @4
    @5
    @75
    @84
    unssbd
    @5
    @75
    @44
    elpw
    sylibr
    jca
    @3
    @76
    @76
    elxp6
    sylanbrc
    abssi
    eqsstri
    ssexi
    a1i
    fnse
    jca
    trud
end
