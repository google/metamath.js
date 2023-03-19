include "con0.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cres.mm"
include "weq.mm"
include "wi.mm"
include "ccnv.mm"
include "wfun.mm"
include "wel.mm"
include "wcel.mm"
include "wal.mm"
include "r2al.mm"
include "simpl.mm"
include "anim1i.mm"
include "imim1i.mm"
include "expd.mm"
include "2alimi.mm"
include "sylbi.mm"
include "sylibr.mm"
include "elequ1.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "notbid.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "elequ2.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "bitri.mm"
include "3bitri.mm"
include "ralcom2.mm"
include "ancri.mm"
include "r19.26-2.mm"
include "syl.mm"
include "wb.mm"
include "fvres.mm"
include "eqeqan12d.mm"
include "ad2antrl.mm"
include "ssel.mm"
include "anim12d.mm"
include "wo.mm"
include "pm3.48.mm"
include "oridm.mm"
include "eqcom.mm"
include "notbii.mm"
include "orbi1i.mm"
include "bitr3i.mm"
include "syl6ibr.mm"
include "con2d.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3.mm"
include "biimprd.mm"
include "syl2an.mm"
include "syl9r.mm"
include "syl6.mm"
include "imp32.mm"
include "sylbid.mm"
include "exp32.mm"
include "a2d.mm"
include "2alimdv.mm"
include "3imtr4g.mm"
include "syl5.mm"
include "imdistani.mm"
include "wfn.mm"
include "fnssres.mm"
include "mpan.mm"
include "cvv.mm"
include "wf.mm"
include "dffn2.mm"
include "wf1.mm"
include "dff13.mm"
include "df-f1.mm"
include "simprbi.mm"
include "sylanb.mm"
include "sylan.mm"

theorem tz7.48lem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vz: setvar z
  let vw: setvar w
  assume tz7.48.1: |- F Fn On

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint x z
  disjoint w x
  disjoint F z
  disjoint F w
  assert |- ( ( A C_ On /\ A. x e. A A. y e. x -. ( F ` x ) = ( F ` y ) ) -> Fun `' ( F |` A ) )

  proof
    cA
    con0
    wss
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    wn
    #
    vy
    @1
    wral
    vx
    cA
    wral
    #
    wa
    @0
    @1
    cF
    cA
    cres
    #
    cfv
    #
    @3
    @8
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @8
    ccnv
    wfun
    #
    @0
    @7
    @14
    @7
    vx
    vy
    wel
    #
    @4
    @2
    wceq
    #
    wn
    #
    wi
    #
    vy
    vx
    wel
    #
    @6
    wi
    #
    wa
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @0
    @14
    @7
    @21
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @23
    @7
    @1
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    #
    @21
    wi
    #
    vy
    wal
    vx
    wal
    #
    @25
    @7
    @26
    @20
    wa
    #
    @6
    wi
    #
    vy
    wal
    vx
    wal
    @30
    @6
    vx
    vy
    cA
    @1
    r2al
    @32
    @29
    vx
    vy
    @32
    @28
    @20
    @6
    @28
    @20
    wa
    @31
    @6
    @28
    @26
    @20
    @26
    @27
    simpl
    anim1i
    imim1i
    expd
    2alimi
    sylbi
    @21
    vx
    vy
    cA
    cA
    r2al
    sylibr
    @25
    @19
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @25
    wa
    @23
    @25
    @33
    @25
    @19
    vx
    cA
    wral
    #
    vy
    cA
    wral
    #
    @33
    @25
    vw
    vx
    wel
    #
    @2
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    wn
    #
    wi
    #
    vw
    cA
    wral
    #
    vx
    cA
    wral
    vw
    vz
    wel
    #
    vz
    cv
    #
    cF
    cfv
    #
    @38
    wceq
    #
    wn
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    cA
    wral
    #
    @35
    @24
    @42
    vx
    cA
    @21
    @41
    vy
    vw
    cA
    vy
    vw
    weq
    #
    @20
    @36
    @6
    @40
    vy
    vw
    vx
    elequ1
    @51
    @5
    @39
    @51
    @4
    @38
    @2
    @3
    @37
    cF
    fveq2
    eqeq2d
    notbid
    imbi12d
    cbvralv
    ralbii
    @42
    @49
    vx
    vz
    cA
    vx
    vz
    weq
    #
    @41
    @48
    vw
    cA
    @52
    @36
    @43
    @40
    @47
    vx
    vz
    vw
    elequ2
    @52
    @39
    @46
    @52
    @2
    @45
    @38
    @1
    @44
    cF
    fveq2
    eqeq1d
    notbid
    imbi12d
    ralbidv
    cbvralv
    @50
    vx
    vz
    wel
    #
    @45
    @2
    wceq
    #
    wn
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    cA
    wral
    @35
    @49
    @57
    vz
    cA
    @48
    @56
    vw
    vx
    cA
    vw
    vx
    weq
    #
    @43
    @53
    @47
    @55
    vw
    vx
    vz
    elequ1
    @58
    @46
    @54
    @58
    @38
    @2
    @45
    @37
    @1
    cF
    fveq2
    eqeq2d
    notbid
    imbi12d
    cbvralv
    ralbii
    @57
    @34
    vz
    vy
    cA
    vz
    vy
    weq
    #
    @56
    @19
    vx
    cA
    @59
    @53
    @16
    @55
    @18
    vz
    vy
    vx
    elequ2
    @59
    @54
    @17
    @59
    @45
    @4
    @2
    @44
    @3
    cF
    fveq2
    eqeq1d
    notbid
    imbi12d
    ralbidv
    cbvralv
    bitri
    3bitri
    @19
    vy
    vx
    cA
    ralcom2
    sylbi
    ancri
    @19
    @21
    vx
    vy
    cA
    cA
    r19.26-2
    sylibr
    syl
    @0
    @28
    @22
    wi
    #
    vy
    wal
    vx
    wal
    @28
    @13
    wi
    #
    vy
    wal
    vx
    wal
    @23
    @14
    @0
    @60
    @61
    vx
    vy
    @0
    @28
    @22
    @13
    @0
    @28
    @22
    @13
    @0
    @28
    @22
    wa
    wa
    @11
    @5
    @12
    @28
    @11
    @5
    wb
    @0
    @22
    @26
    @27
    @9
    @2
    @10
    @4
    @1
    cA
    cF
    fvres
    @3
    cA
    cF
    fvres
    eqeqan12d
    ad2antrl
    @0
    @28
    @22
    @5
    @12
    wi
    #
    @0
    @28
    @1
    con0
    wcel
    #
    @3
    con0
    wcel
    #
    wa
    #
    @22
    @62
    wi
    @0
    @26
    @63
    @27
    @64
    cA
    con0
    @1
    ssel
    cA
    con0
    @3
    ssel
    anim12d
    @22
    @5
    @16
    @20
    wo
    #
    wn
    #
    @65
    @12
    @22
    @66
    @5
    @22
    @66
    @18
    @6
    wo
    #
    @6
    @16
    @18
    @20
    @6
    pm3.48
    @6
    @6
    @6
    wo
    @68
    @6
    oridm
    @6
    @18
    @6
    @5
    @17
    @2
    @4
    eqcom
    notbii
    orbi1i
    bitr3i
    syl6ibr
    con2d
    @63
    @1
    word
    #
    @3
    word
    #
    @67
    @12
    wi
    @64
    @1
    eloni
    @3
    eloni
    @69
    @70
    wa
    @12
    @67
    @1
    @3
    ordtri3
    biimprd
    syl2an
    syl9r
    syl6
    imp32
    sylbid
    exp32
    a2d
    2alimdv
    @22
    vx
    vy
    cA
    cA
    r2al
    @13
    vx
    vy
    cA
    cA
    r2al
    3imtr4g
    syl5
    imdistani
    @0
    @8
    cA
    wfn
    #
    @14
    @15
    cF
    con0
    wfn
    @0
    @71
    tz7.48.1
    con0
    cA
    cF
    fnssres
    mpan
    @71
    cA
    cvv
    @8
    wf
    #
    @14
    @15
    cA
    @8
    dffn2
    @72
    @14
    wa
    #
    @72
    @15
    @73
    cA
    cvv
    @8
    wf1
    @72
    @15
    wa
    vx
    vy
    cA
    cvv
    @8
    dff13
    cA
    cvv
    @8
    df-f1
    bitr3i
    simprbi
    sylanb
    sylan
    syl
end
