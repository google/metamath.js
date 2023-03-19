include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "abscld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "clt.mm"
include "wb.mm"
include "avglt1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "avglt2.mm"
include "eliood.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "resubcld.mm"
include "remulcld.mm"
include "cc.mm"
include "subcld.mm"
include "abs2difd.mm"
include "simpll.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "elioore.mm"
include "adantl.mm"
include "simpr.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "wf.mm"
include "cdv.mm"
include "cdm.mm"
include "wceq.mm"
include "wral.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "dvbdfbdioolem1.mm"
include "simprd.mm"
include "wn.mm"
include "cc0.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "subeq0bd.mm"
include "abs00bd.mm"
include "0red.mm"
include "wss.mm"
include "ioossre.mm"
include "dvfre.mm"
include "sylancl.mm"
include "eleqtrrd.mm"
include "absge0d.mm"
include "rspccva.mm"
include "letrd.mm"
include "posdifd.mm"
include "ltled.mm"
include "mulge0d.mm"
include "eqbrtrd.mm"
include "ad4ant14.mm"
include "ad3antrrr.mm"
include "nltled.mm"
include "wne.mm"
include "neqne.mm"
include "leneltd.mm"
include "abssubd.mm"
include "ad2antlr.mm"
include "pm2.61dan.mm"
include "leadd1dd.mm"
include "npcand.mm"
include "mulcld.mm"
include "addcomd.mm"
include "syl5eq.mm"
include "3brtr4d.mm"
include "ralrimiva.mm"

theorem dvbdfbdioolem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cM: class M
  let vy: setvar y
  let vk: setvar k
  assume dvbdfbdioolem2.a: |- ( ph -> A e. RR )
  assume dvbdfbdioolem2.b: |- ( ph -> B e. RR )
  assume dvbdfbdioolem2.altb: |- ( ph -> A < B )
  assume dvbdfbdioolem2.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume dvbdfbdioolem2.dmdv: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvbdfbdioolem2.k: |- ( ph -> K e. RR )
  assume dvbdfbdioolem2.dvbd: |- ( ph -> A. x e. ( A (,) B ) ( abs ` ( ( RR _D F ) ` x ) ) <_ K )
  assume dvbdfbdioolem2.m: |- M = ( ( abs ` ( F ` ( ( A + B ) / 2 ) ) ) + ( K x. ( B - A ) ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint K x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  disjoint K y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> A. x e. ( A (,) B ) ( abs ` ( F ` x ) ) <_ M )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cM
    cle
    wbr
    vx
    cA
    cB
    cioo
    co
    #
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @2
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cmin
    co
    #
    @9
    caddc
    co
    #
    cK
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    @9
    caddc
    co
    #
    @2
    cM
    cle
    @5
    @10
    @13
    @9
    @5
    @2
    @9
    @5
    @1
    @5
    @1
    wph
    @3
    cr
    @0
    cF
    dvbdfbdioolem2.f
    ffvelrnda
    recnd
    #
    abscld
    #
    wph
    @9
    cr
    wcel
    @4
    wph
    @8
    wph
    @8
    wph
    @3
    cr
    @7
    cF
    dvbdfbdioolem2.f
    wph
    cA
    cB
    @7
    wph
    cA
    dvbdfbdioolem2.a
    rexrd
    #
    wph
    cB
    dvbdfbdioolem2.b
    rexrd
    #
    wph
    @6
    wph
    cA
    cB
    dvbdfbdioolem2.a
    dvbdfbdioolem2.b
    readdcld
    rehalfcld
    #
    wph
    cA
    cB
    clt
    wbr
    #
    cA
    @7
    clt
    wbr
    #
    dvbdfbdioolem2.altb
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @20
    @21
    wb
    dvbdfbdioolem2.a
    dvbdfbdioolem2.b
    cA
    cB
    avglt1
    syl2anc
    mpbid
    wph
    @20
    @7
    cB
    clt
    wbr
    #
    dvbdfbdioolem2.altb
    wph
    @22
    @23
    @20
    @24
    wb
    dvbdfbdioolem2.a
    dvbdfbdioolem2.b
    cA
    cB
    avglt2
    syl2anc
    mpbid
    #
    eliood
    #
    ffvelrnd
    recnd
    #
    abscld
    #
    adantr
    #
    resubcld
    #
    @5
    cK
    @12
    wph
    cK
    cr
    wcel
    #
    @4
    dvbdfbdioolem2.k
    adantr
    @5
    cB
    cA
    wph
    @23
    @4
    dvbdfbdioolem2.b
    adantr
    wph
    @22
    @4
    dvbdfbdioolem2.a
    adantr
    resubcld
    remulcld
    #
    @29
    @5
    @10
    @1
    @8
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    @30
    @5
    @33
    @5
    @1
    @8
    @15
    wph
    @8
    cc
    wcel
    #
    @4
    @27
    adantr
    #
    subcld
    abscld
    @32
    @5
    @1
    @8
    @15
    @36
    abs2difd
    @5
    @7
    @0
    clt
    wbr
    #
    @34
    @13
    cle
    wbr
    #
    @5
    @37
    wa
    #
    wph
    @0
    @7
    cB
    cioo
    co
    wcel
    #
    @38
    wph
    @4
    @37
    simpll
    @39
    @7
    cB
    @0
    wph
    @7
    cxr
    wcel
    @4
    @37
    wph
    @7
    @19
    rexrd
    ad2antrr
    wph
    cB
    cxr
    wcel
    #
    @4
    @37
    @18
    ad2antrr
    @5
    @0
    cr
    wcel
    #
    @37
    @4
    @42
    wph
    @0
    cA
    cB
    elioore
    #
    adantl
    #
    adantr
    @5
    @37
    simpr
    @5
    @0
    cB
    clt
    wbr
    #
    @37
    @5
    cA
    cxr
    wcel
    #
    @41
    @4
    @45
    wph
    @46
    @4
    @17
    adantr
    wph
    @41
    @4
    @18
    adantr
    wph
    @4
    simpr
    #
    cA
    cB
    @0
    iooltub
    syl3anc
    adantr
    eliood
    wph
    @40
    wa
    #
    @34
    cK
    @0
    @7
    cmin
    co
    cmul
    co
    cle
    wbr
    @38
    @48
    vy
    cA
    cB
    @7
    @0
    cF
    cK
    wph
    @22
    @40
    dvbdfbdioolem2.a
    adantr
    wph
    @23
    @40
    dvbdfbdioolem2.b
    adantr
    wph
    @3
    cr
    cF
    wf
    #
    @40
    dvbdfbdioolem2.f
    adantr
    wph
    cr
    cF
    cdv
    co
    #
    cdm
    #
    @3
    wceq
    #
    @40
    dvbdfbdioolem2.dmdv
    adantr
    wph
    @31
    @40
    dvbdfbdioolem2.k
    adantr
    wph
    vy
    cv
    #
    @50
    cfv
    #
    cabs
    cfv
    #
    cK
    cle
    wbr
    #
    vy
    @3
    wral
    #
    @40
    wph
    @0
    @50
    cfv
    #
    cabs
    cfv
    #
    cK
    cle
    wbr
    #
    vx
    @3
    wral
    #
    @57
    dvbdfbdioolem2.dvbd
    @60
    @56
    vx
    vy
    @3
    @0
    @53
    wceq
    #
    @59
    @55
    cK
    cle
    @62
    @58
    @54
    cabs
    @0
    @53
    @50
    fveq2
    fveq2d
    breq1d
    cbvralv
    sylib
    #
    adantr
    wph
    @7
    @3
    wcel
    #
    @40
    @26
    adantr
    wph
    @40
    simpr
    dvbdfbdioolem1
    simprd
    syl2anc
    @5
    @37
    wn
    #
    wa
    #
    @7
    @0
    wceq
    #
    @38
    wph
    @67
    @38
    @4
    @65
    wph
    @67
    wa
    #
    @34
    cc0
    @13
    cle
    @68
    @33
    @68
    @1
    @8
    @68
    @1
    @8
    cc
    @67
    @1
    @8
    wceq
    wph
    @67
    @8
    @1
    @7
    @0
    cF
    fveq2
    eqcomd
    adantl
    #
    wph
    @35
    @67
    @27
    adantr
    eqeltrd
    @69
    subeq0bd
    abs00bd
    @68
    cK
    @12
    wph
    @31
    @67
    dvbdfbdioolem2.k
    adantr
    @68
    cB
    cA
    wph
    @23
    @67
    dvbdfbdioolem2.b
    adantr
    wph
    @22
    @67
    dvbdfbdioolem2.a
    adantr
    resubcld
    wph
    cc0
    cK
    cle
    wbr
    @67
    wph
    cc0
    @7
    @50
    cfv
    #
    cabs
    cfv
    #
    cK
    wph
    0red
    #
    wph
    @70
    wph
    @70
    wph
    @51
    cr
    @7
    @50
    wph
    @49
    @3
    cr
    wss
    @51
    cr
    @50
    wf
    dvbdfbdioolem2.f
    cA
    cB
    ioossre
    @3
    cF
    dvfre
    sylancl
    wph
    @7
    @3
    @51
    @26
    dvbdfbdioolem2.dmdv
    eleqtrrd
    ffvelrnd
    recnd
    #
    abscld
    dvbdfbdioolem2.k
    wph
    @70
    @73
    absge0d
    wph
    @61
    @64
    @71
    cK
    cle
    wbr
    #
    dvbdfbdioolem2.dvbd
    @26
    @60
    @74
    vx
    @7
    @3
    @0
    @7
    wceq
    #
    @59
    @71
    cK
    cle
    @75
    @58
    @70
    cabs
    @0
    @7
    @50
    fveq2
    fveq2d
    breq1d
    rspccva
    syl2anc
    letrd
    adantr
    wph
    cc0
    @12
    cle
    wbr
    @67
    wph
    cc0
    @12
    @72
    wph
    cB
    cA
    dvbdfbdioolem2.b
    dvbdfbdioolem2.a
    resubcld
    wph
    @20
    cc0
    @12
    clt
    wbr
    dvbdfbdioolem2.altb
    wph
    cA
    cB
    dvbdfbdioolem2.a
    dvbdfbdioolem2.b
    posdifd
    mpbid
    ltled
    adantr
    mulge0d
    eqbrtrd
    ad4ant14
    @66
    @67
    wn
    #
    wa
    #
    @5
    @0
    @7
    clt
    wbr
    #
    @38
    @5
    @65
    @76
    simpll
    @77
    @0
    @7
    @5
    @42
    @65
    @76
    @44
    ad2antrr
    wph
    @7
    cr
    wcel
    #
    @4
    @65
    @76
    @19
    ad3antrrr
    @66
    @0
    @7
    cle
    wbr
    @76
    @66
    @0
    @7
    @5
    @42
    @65
    @44
    adantr
    wph
    @79
    @4
    @65
    @19
    ad2antrr
    @5
    @65
    simpr
    nltled
    adantr
    @76
    @7
    @0
    wne
    @66
    @7
    @0
    neqne
    adantl
    leneltd
    @5
    @78
    wa
    #
    @34
    @8
    @1
    cmin
    co
    cabs
    cfv
    #
    @13
    cle
    @5
    @34
    @81
    wceq
    @78
    @5
    @1
    @8
    @15
    @36
    abssubd
    adantr
    @80
    @81
    cK
    @7
    @0
    cmin
    co
    cmul
    co
    cle
    wbr
    @81
    @13
    cle
    wbr
    @80
    vy
    cA
    cB
    @0
    @7
    cF
    cK
    wph
    @22
    @4
    @78
    dvbdfbdioolem2.a
    ad2antrr
    wph
    @23
    @4
    @78
    dvbdfbdioolem2.b
    ad2antrr
    wph
    @49
    @4
    @78
    dvbdfbdioolem2.f
    ad2antrr
    wph
    @52
    @4
    @78
    dvbdfbdioolem2.dmdv
    ad2antrr
    wph
    @31
    @4
    @78
    dvbdfbdioolem2.k
    ad2antrr
    wph
    @57
    @4
    @78
    @63
    ad2antrr
    @5
    @4
    @78
    @47
    adantr
    @80
    @0
    cB
    @7
    @4
    @0
    cxr
    wcel
    wph
    @78
    @4
    @0
    @43
    rexrd
    ad2antlr
    wph
    @41
    @4
    @78
    @18
    ad2antrr
    wph
    @79
    @4
    @78
    @19
    ad2antrr
    @5
    @78
    simpr
    wph
    @24
    @4
    @78
    @25
    ad2antrr
    eliood
    dvbdfbdioolem1
    simprd
    eqbrtrd
    syl2anc
    pm2.61dan
    pm2.61dan
    letrd
    leadd1dd
    @5
    @11
    @2
    @5
    @2
    @9
    @5
    @2
    @16
    recnd
    @5
    @9
    @29
    recnd
    npcand
    eqcomd
    wph
    cM
    @14
    wceq
    @4
    wph
    cM
    @9
    @13
    caddc
    co
    @14
    dvbdfbdioolem2.m
    wph
    @9
    @13
    wph
    @9
    @28
    recnd
    wph
    cK
    @12
    wph
    cK
    dvbdfbdioolem2.k
    recnd
    wph
    cB
    cA
    wph
    cB
    dvbdfbdioolem2.b
    recnd
    wph
    cA
    dvbdfbdioolem2.a
    recnd
    subcld
    mulcld
    addcomd
    syl5eq
    adantr
    3brtr4d
    ralrimiva
end
