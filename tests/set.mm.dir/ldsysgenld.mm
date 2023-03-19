include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cpw.mm"
include "wcel.mm"
include "c0.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "csiga.mm"
include "cfv.mm"
include "pwsiga.mm"
include "syl.mm"
include "sigaldsys.mm"
include "sseldi.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "sselpwd.mm"
include "isldsys.mm"
include "simprbi.mm"
include "simp1d.mm"
include "adantl.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "0ex.mm"
include "elintrab.mm"
include "sylibr.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfel.mm"
include "nfan.mm"
include "simplr.mm"
include "vex.mm"
include "biimpi.mm"
include "r19.21bi.mm"
include "imp.mm"
include "simp2d.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "cvv.mm"
include "difexg.mm"
include "elintrabg.mm"
include "3syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "nfpw.mm"
include "simpr.mm"
include "simpllr.mm"
include "syl21anc.mm"
include "ssrdv.mm"
include "sspwb.mm"
include "sylib.mm"
include "simp-4r.mm"
include "sseldd.mm"
include "simp3d.mm"
include "vuniex.mm"
include "3jca.mm"
include "jca.mm"

theorem ldsysgenld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cL: class L
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vu: setvar u
  let cS: class S
  assume isldsys.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume ldsysgenld.1: |- ( ph -> O e. V )
  assume ldsysgenld.2: |- ( ph -> A C_ ~P O )

  disjoint s y
  disjoint L t
  disjoint O s
  disjoint O t
  disjoint O x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint V x
  disjoint t y
  disjoint A s
  disjoint A t
  disjoint A x
  disjoint L s
  disjoint L x
  disjoint ph t
  disjoint ph x
  disjoint s u
  disjoint u y
  disjoint S s
  disjoint S x
  disjoint A u
  disjoint t u
  disjoint u x
  disjoint L u
  disjoint ph u
  assert |- ( ph -> |^| { t e. L | A C_ t } e. L )

  proof
    wph
    cA
    vt
    cv
    #
    wss
    #
    vt
    cL
    crab
    #
    cint
    #
    cO
    cpw
    #
    cpw
    #
    wcel
    #
    c0
    @3
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @3
    wcel
    #
    vx
    @3
    wral
    #
    @8
    com
    cdom
    wbr
    vy
    @8
    vy
    cv
    wdisj
    wa
    #
    @8
    cuni
    #
    @3
    wcel
    #
    wi
    #
    vx
    @3
    cpw
    #
    wral
    #
    w3a
    #
    wa
    @3
    cL
    wcel
    wph
    @6
    @18
    wph
    @3
    @4
    cO
    csiga
    cfv
    #
    wph
    cO
    cV
    wcel
    #
    @4
    @19
    wcel
    ldsysgenld.1
    cO
    cV
    pwsiga
    syl
    #
    wph
    @4
    @2
    wcel
    #
    @3
    @4
    wss
    wph
    @4
    cL
    wcel
    cA
    @4
    wss
    #
    @22
    wph
    @19
    cL
    @4
    vx
    vy
    cL
    cO
    vs
    isldsys.l
    sigaldsys
    @21
    sseldi
    ldsysgenld.2
    @1
    @23
    vt
    @4
    cL
    @0
    @4
    cA
    sseq2
    elrab
    sylanbrc
    @4
    @2
    intss1
    syl
    sselpwd
    wph
    @7
    @11
    @17
    wph
    @1
    c0
    @0
    wcel
    #
    wi
    #
    vt
    cL
    wral
    @7
    wph
    @25
    vt
    cL
    wph
    @0
    cL
    wcel
    #
    wa
    @24
    @1
    @26
    @24
    wph
    @26
    @24
    @9
    @0
    wcel
    #
    vx
    @0
    wral
    #
    @12
    @13
    @0
    wcel
    #
    wi
    #
    vx
    @0
    cpw
    #
    wral
    #
    @26
    @0
    @5
    wcel
    @24
    @28
    @32
    w3a
    vx
    vy
    @0
    cL
    cO
    vs
    isldsys.l
    isldsys
    simprbi
    #
    simp1d
    adantl
    a1d
    ralrimiva
    @1
    vt
    c0
    cL
    0ex
    elintrab
    sylibr
    wph
    @10
    vx
    @3
    wph
    @8
    @3
    wcel
    #
    wa
    #
    @10
    @1
    @27
    wi
    #
    vt
    cL
    wral
    #
    @35
    @36
    vt
    cL
    wph
    @34
    vt
    wph
    vt
    nfv
    #
    vt
    @8
    @3
    vt
    @8
    nfcv
    #
    vt
    @2
    @1
    vt
    cL
    nfrab1
    nfint
    #
    nfel
    nfan
    @35
    @26
    @36
    @35
    @26
    wa
    #
    @1
    @27
    @41
    @1
    wa
    @26
    @8
    @0
    wcel
    #
    @27
    @35
    @26
    @1
    simplr
    @41
    @1
    @42
    @35
    @1
    @42
    wi
    #
    vt
    cL
    @34
    @43
    vt
    cL
    wral
    #
    wph
    @34
    @44
    @1
    vt
    @8
    cL
    vx
    vex
    elintrab
    biimpi
    adantl
    r19.21bi
    imp
    @26
    @27
    vx
    @0
    @26
    @24
    @28
    @32
    @33
    simp2d
    r19.21bi
    syl2anc
    ex
    ex
    ralrimi
    wph
    @10
    @37
    wb
    #
    @34
    wph
    @20
    @9
    cvv
    wcel
    @45
    ldsysgenld.1
    cO
    @8
    cV
    difexg
    @1
    vt
    @9
    cL
    cvv
    elintrabg
    3syl
    adantr
    mpbird
    ralrimiva
    wph
    @15
    vx
    @16
    wph
    @8
    @16
    wcel
    #
    wa
    #
    @12
    @14
    @47
    @12
    wa
    #
    @1
    @29
    wi
    #
    vt
    cL
    wral
    @14
    @48
    @49
    vt
    cL
    @47
    @12
    vt
    wph
    @46
    vt
    @38
    vt
    @8
    @16
    @39
    vt
    @3
    @40
    nfpw
    nfel
    nfan
    @12
    vt
    nfv
    nfan
    @48
    @26
    @49
    @48
    @26
    wa
    #
    @1
    @29
    @50
    @1
    wa
    #
    @26
    @8
    @31
    wcel
    #
    @12
    @29
    @48
    @26
    @1
    simplr
    @51
    @16
    @31
    @8
    @51
    @3
    @0
    wss
    @16
    @31
    wss
    @51
    vu
    @3
    @0
    @51
    vu
    cv
    #
    @3
    wcel
    #
    @53
    @0
    wcel
    #
    @51
    @54
    wa
    @54
    @26
    @1
    @55
    @51
    @54
    simpr
    @48
    @26
    @1
    @54
    simpllr
    @50
    @1
    @54
    simplr
    @54
    @26
    wa
    @1
    @55
    @54
    @1
    @55
    wi
    #
    vt
    cL
    @54
    @56
    vt
    cL
    wral
    @1
    vt
    @53
    cL
    vu
    vex
    elintrab
    biimpi
    r19.21bi
    imp
    syl21anc
    ex
    ssrdv
    @3
    @0
    sspwb
    sylib
    wph
    @46
    @12
    @26
    @1
    simp-4r
    sseldd
    @47
    @12
    @26
    @1
    simpllr
    @26
    @52
    wa
    @12
    @29
    @26
    @30
    vx
    @31
    @26
    @24
    @28
    @32
    @33
    simp3d
    r19.21bi
    imp
    syl21anc
    ex
    ex
    ralrimi
    @1
    vt
    @13
    cL
    vx
    vuniex
    elintrab
    sylibr
    ex
    ralrimiva
    3jca
    jca
    vx
    vy
    @3
    cL
    cO
    vs
    isldsys.l
    isldsys
    sylibr
end
