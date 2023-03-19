include "cin.mm"
include "ciun.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wceq.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfin.mm"
include "csbeq1a.mm"
include "ineq1d.mm"
include "cbviun.mm"
include "sumeq1i.mm"
include "a1i.mm"
include "wss.mm"
include "wcel.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "eliun.mm"
include "biimpi.mm"
include "df-rex.mm"
include "sylib.mm"
include "nfiu1.mm"
include "nfel.mm"
include "wi.mm"
include "simpl.mm"
include "ne0i.mm"
include "adantl.mm"
include "jca.mm"
include "nfv.mm"
include "nfci.mm"
include "nfne.mm"
include "neeq1d.mm"
include "elrabf.mm"
include "sylibr.mm"
include "simpr.mm"
include "eximd.mm"
include "mpd.mm"
include "rgen.mm"
include "dfss3.mm"
include "mpbir.mm"
include "elrabi.mm"
include "ssriv.mm"
include "iunss1.mm"
include "ax-mp.mm"
include "eqssi.mm"
include "disjinfi.mm"
include "cfn.mm"
include "inss2.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wdisj.mm"
include "inss1.mm"
include "rgenw.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "cbvdisj.mm"
include "disjss2.mm"
include "sylc.mm"
include "disjss1.mm"
include "cc.mm"
include "ad2antrl.mm"
include "sseli.mm"
include "w3a.mm"
include "nf3an.mm"
include "nfim.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "3anbi23d.mm"
include "imbi1d.mm"
include "chvar.mm"
include "syl3anc.mm"
include "fsumiun.mm"
include "sumeq1d.mm"
include "nfrab1.mm"
include "nfsum.mm"
include "cbvsum.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem fsumiunss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume fsumiunss.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume fsumiunss.dj: |- ( ph -> Disj_ x e. A B )
  assume fsumiunss.c: |- ( ( ph /\ x e. A /\ k e. B ) -> C e. CC )
  assume fsumiunss.fi: |- ( ph -> D e. Fin )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint C x
  disjoint D k
  disjoint D x
  disjoint V x
  disjoint k ph
  disjoint ph x
  disjoint A y
  disjoint k y
  disjoint x y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint D y
  disjoint D z
  disjoint ph y
  assert |- ( ph -> sum_ k e. U_ x e. A ( B i^i D ) C = sum_ x e. { x e. A | ( B i^i D ) =/= (/) } sum_ k e. ( B i^i D ) C )

  proof
    wph
    vx
    cA
    cB
    cD
    cin
    #
    ciun
    #
    cC
    vk
    csu
    #
    vy
    cA
    vx
    vy
    cv
    #
    cB
    csb
    #
    cD
    cin
    #
    ciun
    #
    cC
    vk
    csu
    #
    vy
    @0
    c0
    wne
    #
    vx
    cA
    crab
    #
    @5
    ciun
    #
    cC
    vk
    csu
    #
    @9
    @0
    cC
    vk
    csu
    #
    vx
    csu
    #
    @2
    @7
    wceq
    wph
    @1
    @6
    cC
    vk
    vx
    vy
    cA
    @0
    @5
    vy
    @0
    nfcv
    vx
    @4
    cD
    vx
    @3
    cB
    nfcsb1v
    #
    vx
    cD
    nfcv
    nfin
    #
    vx
    cv
    #
    @3
    wceq
    #
    cB
    @4
    cD
    vx
    @3
    cB
    csbeq1a
    #
    ineq1d
    #
    cbviun
    sumeq1i
    a1i
    @7
    @11
    wceq
    wph
    @6
    @10
    cC
    vk
    @6
    @10
    @6
    @10
    wss
    vz
    cv
    #
    @10
    wcel
    #
    vz
    @6
    wral
    @21
    vz
    @6
    @20
    @6
    wcel
    #
    @20
    @5
    wcel
    #
    vy
    @9
    wrex
    #
    @21
    @22
    @3
    @9
    wcel
    #
    @23
    wa
    #
    vy
    wex
    #
    @24
    @22
    @3
    cA
    wcel
    #
    @23
    wa
    #
    vy
    wex
    #
    @27
    @22
    @23
    vy
    cA
    wrex
    #
    @30
    @22
    @31
    vy
    @20
    cA
    @5
    eliun
    biimpi
    @23
    vy
    cA
    df-rex
    sylib
    @22
    @29
    @26
    vy
    vy
    @20
    @6
    vy
    @20
    nfcv
    vy
    cA
    @5
    nfiu1
    nfel
    @29
    @26
    wi
    @22
    @29
    @25
    @23
    @29
    @28
    @5
    c0
    wne
    #
    wa
    @25
    @29
    @28
    @32
    @28
    @23
    simpl
    @23
    @32
    @28
    @5
    @20
    ne0i
    adantl
    jca
    @8
    @32
    vx
    @3
    cA
    vx
    @3
    nfcv
    vx
    vy
    cA
    @28
    vx
    nfv
    #
    nfci
    vx
    @5
    c0
    @15
    vx
    c0
    nfcv
    nfne
    @17
    @0
    @5
    c0
    @19
    neeq1d
    elrabf
    sylibr
    @28
    @23
    simpr
    jca
    a1i
    eximd
    mpd
    @23
    vy
    @9
    df-rex
    sylibr
    vy
    @20
    @9
    @5
    eliun
    sylibr
    rgen
    vz
    @6
    @10
    dfss3
    mpbir
    @9
    cA
    wss
    #
    @10
    @6
    wss
    vy
    @9
    cA
    @8
    vx
    @3
    cA
    elrabi
    #
    ssriv
    #
    vy
    @9
    cA
    @5
    iunss1
    ax-mp
    eqssi
    sumeq1i
    a1i
    wph
    @11
    @9
    @5
    cC
    vk
    csu
    #
    vy
    csu
    #
    @13
    wph
    vy
    @9
    @5
    cC
    vk
    wph
    vx
    cA
    cB
    cD
    cV
    fsumiunss.b
    fsumiunss.dj
    fsumiunss.fi
    disjinfi
    wph
    @5
    cfn
    wcel
    #
    @25
    wph
    cD
    cfn
    wcel
    @5
    cD
    wss
    #
    @39
    fsumiunss.fi
    @40
    wph
    @4
    cD
    inss2
    a1i
    cD
    @5
    ssfi
    syl2anc
    adantr
    wph
    @34
    vy
    cA
    @5
    wdisj
    #
    vy
    @9
    @5
    wdisj
    @34
    wph
    @36
    a1i
    wph
    @5
    @4
    wss
    #
    vy
    cA
    wral
    #
    vy
    cA
    @4
    wdisj
    #
    @41
    @43
    wph
    @42
    vy
    cA
    @4
    cD
    inss1
    #
    rgenw
    a1i
    wph
    vx
    cA
    cB
    wdisj
    @44
    fsumiunss.dj
    vy
    vx
    cA
    @4
    cB
    @14
    vy
    cB
    nfcv
    @17
    cB
    @4
    wceq
    #
    wi
    #
    @3
    @16
    wceq
    #
    @4
    cB
    wceq
    #
    wi
    #
    @18
    @47
    @48
    @46
    wi
    @50
    @17
    @48
    @46
    @16
    @3
    eqcom
    imbi1i
    @46
    @49
    @48
    cB
    @4
    eqcom
    imbi2i
    bitri
    mpbi
    #
    cbvdisj
    sylibr
    vy
    cA
    @5
    @4
    disjss2
    sylc
    vy
    @9
    cA
    @5
    disjss1
    sylc
    wph
    @25
    vk
    cv
    #
    @5
    wcel
    #
    wa
    #
    wa
    wph
    @28
    @52
    @4
    wcel
    #
    cC
    cc
    wcel
    #
    wph
    @54
    simpl
    @25
    @28
    wph
    @53
    @35
    ad2antrl
    @54
    @55
    wph
    @53
    @55
    @25
    @5
    @4
    @52
    @45
    sseli
    adantl
    adantl
    wph
    @16
    cA
    wcel
    #
    @52
    cB
    wcel
    #
    w3a
    #
    @56
    wi
    wph
    @28
    @55
    w3a
    #
    @56
    wi
    vx
    vy
    @60
    @56
    vx
    wph
    @28
    @55
    vx
    wph
    vx
    nfv
    @33
    vx
    @52
    @4
    vx
    @52
    nfcv
    @14
    nfel
    nf3an
    @56
    vx
    nfv
    nfim
    @17
    @59
    @60
    @56
    @17
    @57
    @28
    @58
    @55
    wph
    @16
    @3
    cA
    eleq1
    @17
    cB
    @4
    @52
    @18
    eleq2d
    3anbi23d
    imbi1d
    fsumiunss.c
    chvar
    syl3anc
    fsumiun
    @38
    @13
    wceq
    wph
    @9
    @37
    @12
    vy
    vx
    @48
    @5
    @0
    cC
    vk
    @48
    @4
    cB
    cD
    @51
    ineq1d
    sumeq1d
    @8
    vx
    cA
    nfrab1
    vy
    @9
    nfcv
    vx
    @5
    cC
    vk
    @15
    vx
    cC
    nfcv
    nfsum
    vy
    @12
    nfcv
    cbvsum
    a1i
    eqtrd
    3eqtrd
end
