include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "crn.mm"
include "wceq.mm"
include "cr.mm"
include "evthicc.mm"
include "reeanv.mm"
include "sylibr.mm"
include "wcel.mm"
include "r19.26.mm"
include "ccncf.mm"
include "wf.mm"
include "adantr.mm"
include "cncff.mm"
include "syl.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "wss.mm"
include "wfn.mm"
include "ffn.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "3anass.mm"
include "syl6bb.mm"
include "ancom.mm"
include "ffvelrnda.mm"
include "biantrurd.mm"
include "syl5bb.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "biimpar.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "ssid.mm"
include "a1i.mm"
include "cc.mm"
include "ax-resscn.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "ivthicc.mm"
include "eqssd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "ex.mm"
include "syl5bir.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem evthicc2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  assume evthicc.1: |- ( ph -> A e. RR )
  assume evthicc.2: |- ( ph -> B e. RR )
  assume evthicc.3: |- ( ph -> A <_ B )
  assume evthicc.4: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint a b
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B w
  disjoint B z
  disjoint F a
  disjoint F b
  disjoint a ph
  disjoint b ph
  disjoint ph w
  disjoint ph z
  disjoint F w
  disjoint F z
  assert |- ( ph -> E. x e. RR E. y e. RR ran F = ( x [,] y ) )

  proof
    wph
    vz
    cv
    #
    cF
    cfv
    #
    va
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vz
    cA
    cB
    cicc
    co
    #
    wral
    #
    vb
    cv
    #
    cF
    cfv
    #
    @1
    cle
    wbr
    #
    vz
    @5
    wral
    #
    wa
    #
    vb
    @5
    wrex
    va
    @5
    wrex
    #
    cF
    crn
    #
    vx
    cv
    #
    vy
    cv
    cicc
    co
    wceq
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    wph
    @6
    va
    @5
    wrex
    @10
    vb
    @5
    wrex
    wa
    @12
    wph
    va
    vz
    vb
    vz
    cA
    cB
    cF
    evthicc.1
    evthicc.2
    evthicc.3
    evthicc.4
    evthicc
    @6
    @10
    va
    vb
    @5
    @5
    reeanv
    sylibr
    wph
    @11
    @15
    va
    vb
    @5
    @5
    @11
    @4
    @9
    wa
    #
    vz
    @5
    wral
    #
    wph
    @2
    @5
    wcel
    #
    @7
    @5
    wcel
    #
    wa
    #
    wa
    #
    @15
    @4
    @9
    vz
    @5
    r19.26
    @21
    @17
    @15
    @21
    @17
    wa
    #
    @8
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @13
    @8
    @3
    cicc
    co
    #
    wceq
    @15
    @21
    @23
    @17
    @21
    @5
    cr
    @7
    cF
    @21
    cF
    @5
    cr
    ccncf
    co
    #
    wcel
    #
    @5
    cr
    cF
    wf
    #
    wph
    @27
    @20
    evthicc.4
    adantr
    #
    @5
    cr
    cF
    cncff
    syl
    #
    wph
    @18
    @19
    simprr
    #
    ffvelrnd
    #
    adantr
    @21
    @24
    @17
    @21
    @5
    cr
    @2
    cF
    @30
    wph
    @18
    @19
    simprl
    #
    ffvelrnd
    #
    adantr
    @22
    @13
    @25
    @22
    @5
    @25
    cF
    wf
    #
    @13
    @25
    wss
    @22
    cF
    @5
    wfn
    #
    @1
    @25
    wcel
    #
    vz
    @5
    wral
    #
    @35
    @22
    @28
    @36
    @21
    @28
    @17
    @30
    adantr
    @5
    cr
    cF
    ffn
    syl
    @21
    @38
    @17
    @21
    @37
    @16
    vz
    @5
    @21
    @0
    @5
    wcel
    #
    wa
    #
    @37
    @1
    cr
    wcel
    #
    @9
    @4
    wa
    #
    wa
    #
    @16
    @40
    @37
    @41
    @9
    @4
    w3a
    #
    @43
    @40
    @23
    @24
    @37
    @44
    wb
    @21
    @23
    @39
    @32
    adantr
    @21
    @24
    @39
    @34
    adantr
    @8
    @3
    @1
    elicc2
    syl2anc
    @41
    @9
    @4
    3anass
    syl6bb
    @16
    @42
    @40
    @43
    @4
    @9
    ancom
    @40
    @41
    @42
    @21
    @5
    cr
    @0
    cF
    @30
    ffvelrnda
    biantrurd
    syl5bb
    bitr4d
    ralbidva
    biimpar
    vz
    @5
    @25
    cF
    ffnfv
    sylanbrc
    @5
    @25
    cF
    frn
    syl
    @21
    @25
    @13
    wss
    @17
    @21
    vx
    cA
    cB
    @5
    cF
    @7
    @2
    wph
    cA
    cr
    wcel
    @20
    evthicc.1
    adantr
    wph
    cB
    cr
    wcel
    @20
    evthicc.2
    adantr
    @31
    @33
    @5
    @5
    wss
    @21
    @5
    ssid
    a1i
    @21
    @26
    @5
    cc
    ccncf
    co
    #
    cF
    cr
    cc
    wss
    cc
    cc
    wss
    @26
    @45
    wss
    ax-resscn
    cc
    ssid
    @5
    cr
    cc
    cncfss
    mp2an
    @29
    sseldi
    @21
    @5
    cr
    @14
    cF
    @30
    ffvelrnda
    ivthicc
    adantr
    eqssd
    vx
    vy
    cr
    cr
    @8
    @3
    @13
    cicc
    rspceov
    syl3anc
    ex
    syl5bir
    rexlimdvva
    mpd
end
