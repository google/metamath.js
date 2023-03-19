include "cv.mm"
include "cotp.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wal.mm"
include "weu.mm"
include "w3a.mm"
include "biimpa.mm"
include "vex.mm"
include "otth.mm"
include "sylibr.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "impancom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "exlimdvv.mm"
include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "wtru.mm"
include "tru.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqcomd.mm"
include "biimpar.mm"
include "jca.mm"
include "a1tru.mm"
include "2thd.mm"
include "3anassrs.mm"
include "sbcied.mm"
include "mpbiri.mm"
include "spesbcd.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfex.mm"
include "sbceq1a.mm"
include "exbidv.mm"
include "spcegf.mm"
include "sylc.mm"
include "2exbidv.mm"
include "excom13.mm"
include "sylib.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "3exbidv.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "alrimiv.mm"
include "otex.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "syl.mm"
include "df-eu.mm"

theorem euotd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume euotd.1: |- ( ph -> A e. _V )
  assume euotd.2: |- ( ph -> B e. _V )
  assume euotd.3: |- ( ph -> C e. _V )
  assume euotd.4: |- ( ph -> ( ps <-> ( a = A /\ b = B /\ c = C ) ) )

  disjoint a b
  disjoint a c
  disjoint a x
  disjoint A a
  disjoint b c
  disjoint b x
  disjoint A b
  disjoint c x
  disjoint A c
  disjoint A x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint ps y
  assert |- ( ph -> E! x E. a E. b E. c ( x = <. a , b , c >. /\ ps ) )

  proof
    wph
    vx
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cotp
    #
    wceq
    #
    wps
    wa
    #
    vc
    wex
    #
    vb
    wex
    va
    wex
    #
    @0
    vy
    cv
    #
    wceq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    #
    @8
    vx
    weu
    wph
    @8
    @0
    cA
    cB
    cC
    cotp
    #
    wceq
    #
    wb
    #
    vx
    wal
    #
    @13
    wph
    @16
    vx
    wph
    @8
    @15
    wph
    @7
    @15
    va
    vb
    wph
    @6
    @15
    vc
    wph
    @5
    wps
    @15
    wph
    wps
    @5
    @15
    wph
    wps
    wa
    #
    @5
    @15
    @18
    @4
    @14
    @0
    @18
    @1
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    @3
    cC
    wceq
    #
    w3a
    #
    @4
    @14
    wceq
    #
    wph
    wps
    @22
    euotd.4
    biimpa
    @1
    @2
    cA
    cB
    @3
    cC
    va
    vex
    vb
    vex
    vc
    vex
    otth
    #
    sylibr
    eqeq2d
    biimpd
    impancom
    expimpd
    exlimdv
    exlimdvv
    wph
    @8
    @15
    @14
    @4
    wceq
    #
    wps
    wa
    #
    vc
    wex
    vb
    wex
    va
    wex
    #
    wph
    @26
    va
    wex
    vb
    wex
    #
    vc
    wex
    #
    @27
    wph
    cC
    cvv
    wcel
    #
    @26
    vc
    cC
    wsbc
    #
    va
    wex
    #
    vb
    wex
    #
    @29
    euotd.3
    wph
    cB
    cvv
    wcel
    #
    @31
    vb
    cB
    wsbc
    #
    va
    wex
    #
    @33
    euotd.2
    wph
    @35
    va
    cA
    wph
    @35
    va
    cA
    wsbc
    wtru
    tru
    wph
    @35
    wtru
    va
    cA
    cvv
    euotd.1
    wph
    @19
    wa
    #
    @31
    wtru
    vb
    cB
    cvv
    wph
    @34
    @19
    euotd.2
    adantr
    @37
    @20
    wa
    @26
    wtru
    vc
    cC
    cvv
    wph
    @30
    @19
    @20
    euotd.3
    ad2antrr
    wph
    @19
    @20
    @21
    @26
    wtru
    wb
    wph
    @22
    wa
    #
    @26
    wtru
    @38
    @25
    wps
    @38
    @4
    @14
    @38
    @22
    @23
    wph
    @22
    simpr
    @24
    sylibr
    eqcomd
    wph
    wps
    @22
    euotd.4
    biimpar
    jca
    @38
    a1tru
    2thd
    3anassrs
    sbcied
    sbcied
    sbcied
    mpbiri
    spesbcd
    @32
    @36
    vb
    cB
    cvv
    vb
    cB
    nfcv
    @35
    vb
    va
    @31
    vb
    cB
    nfsbc1v
    nfex
    @20
    @31
    @35
    va
    @31
    vb
    cB
    sbceq1a
    exbidv
    spcegf
    sylc
    @28
    @33
    vc
    cC
    cvv
    vc
    cC
    nfcv
    @32
    vc
    vb
    @31
    vc
    va
    @26
    vc
    cC
    nfsbc1v
    nfex
    nfex
    @21
    @26
    @31
    vb
    va
    @26
    vc
    cC
    sbceq1a
    2exbidv
    spcegf
    sylc
    @26
    vc
    vb
    va
    excom13
    sylib
    @15
    @6
    @26
    va
    vb
    vc
    @15
    @5
    @25
    wps
    @0
    @14
    @4
    eqeq1
    anbi1d
    3exbidv
    syl5ibrcom
    impbid
    alrimiv
    @12
    @17
    vy
    @14
    cA
    cB
    cC
    otex
    @9
    @14
    wceq
    #
    @11
    @16
    vx
    @39
    @10
    @15
    @8
    @9
    @14
    @0
    eqeq2
    bibi2d
    albidv
    spcev
    syl
    @8
    vx
    vy
    df-eu
    sylibr
end
