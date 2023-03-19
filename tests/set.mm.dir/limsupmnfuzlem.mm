include "clsp.mm"
include "cfv.mm"
include "cmnf.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cuz.mm"
include "nfcv.mm"
include "wss.mm"
include "uzssre.mm"
include "eqsstri.mm"
include "a1i.mm"
include "limsupmnf.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "biimpi.mm"
include "wcel.mm"
include "w3a.mm"
include "cceil.mm"
include "cif.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "cz.mm"
include "ad2antrr.mm"
include "ceilcl.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "eluzd.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "uzidd2.mm"
include "pm2.61dan.mm"
include "3adant3.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simplr.mm"
include "sseldi.mm"
include "adantr.mm"
include "eluzelre.mm"
include "zred.mm"
include "ceilge.mm"
include "max2.mm"
include "syl2anc.mm"
include "letrd.mm"
include "eluzle.mm"
include "3adantl3.mm"
include "simpl3.mm"
include "eluzelz.mm"
include "max1.mm"
include "syl2an.mm"
include "rspa.mm"
include "mpd.mm"
include "ex.mm"
include "ralrimi.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "imp.mm"
include "sylan2.mm"
include "wb.mm"
include "rexss.mm"
include "ax-mp.mm"
include "nfan.mm"
include "simp1r.mm"
include "eqid.mm"
include "eluzelz2.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "3adant1r.mm"
include "reximdv.mm"
include "impbid.mm"
include "bitrd.mm"

theorem limsupmnfuzlem
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  assume limsupmnfuzlem.1: |- ( ph -> M e. ZZ )
  assume limsupmnfuzlem.2: |- Z = ( ZZ>= ` M )
  assume limsupmnfuzlem.3: |- ( ph -> F : Z --> RR* )

  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint M j
  disjoint M k
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint F i
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint Z i
  disjoint i ph
  assert |- ( ph -> ( ( limsup ` F ) = -oo <-> A. x e. RR E. k e. Z A. j e. ( ZZ>= ` k ) ( F ` j ) <_ x ) )

  proof
    wph
    cF
    clsp
    cfv
    cmnf
    wceq
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    @1
    cF
    cfv
    vx
    cv
    cle
    wbr
    #
    wi
    #
    vj
    cZ
    wral
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wral
    @3
    vj
    @0
    cuz
    cfv
    #
    wral
    #
    vk
    cZ
    wrex
    #
    vx
    cr
    wral
    wph
    vx
    cZ
    vj
    vk
    cF
    vj
    cF
    nfcv
    cZ
    cr
    wss
    #
    wph
    cZ
    cM
    cuz
    cfv
    cr
    limsupmnfuzlem.2
    cM
    uzssre
    eqsstri
    #
    a1i
    limsupmnfuzlem.3
    limsupmnf
    wph
    @6
    @9
    vx
    cr
    wph
    @6
    @9
    wph
    @6
    @9
    @6
    wph
    vi
    cv
    #
    @1
    cle
    wbr
    #
    @3
    wi
    #
    vj
    cZ
    wral
    #
    vi
    cr
    wrex
    #
    @9
    @6
    @16
    @5
    @15
    vk
    vi
    cr
    @0
    @12
    wceq
    #
    @4
    @14
    vj
    cZ
    @17
    @2
    @13
    @3
    @0
    @12
    @1
    cle
    breq1
    imbi1d
    ralbidv
    cbvrexv
    biimpi
    wph
    @16
    @9
    wph
    @15
    @9
    vi
    cr
    wph
    @12
    cr
    wcel
    #
    @15
    @9
    wph
    @18
    @15
    w3a
    #
    cM
    @12
    cceil
    cfv
    #
    cle
    wbr
    #
    @20
    cM
    cif
    #
    cZ
    wcel
    #
    @3
    vj
    @22
    cuz
    cfv
    #
    wral
    #
    @9
    wph
    @18
    @23
    @15
    wph
    @18
    wa
    #
    @21
    @23
    @26
    @21
    wa
    #
    @22
    @20
    cZ
    @21
    @22
    @20
    wceq
    @26
    @21
    @20
    cM
    iftrue
    adantl
    @27
    cM
    @20
    cZ
    limsupmnfuzlem.2
    wph
    cM
    cz
    wcel
    #
    @18
    @21
    limsupmnfuzlem.1
    ad2antrr
    @18
    @20
    cz
    wcel
    wph
    @21
    @12
    ceilcl
    #
    ad2antlr
    @26
    @21
    simpr
    eluzd
    eqeltrd
    @26
    @21
    wn
    #
    wa
    @22
    cM
    cZ
    @30
    @22
    cM
    wceq
    @26
    @21
    @20
    cM
    iffalse
    adantl
    wph
    cM
    cZ
    wcel
    @18
    @30
    wph
    cM
    cZ
    limsupmnfuzlem.1
    limsupmnfuzlem.2
    uzidd2
    #
    ad2antrr
    eqeltrd
    pm2.61dan
    #
    3adant3
    @19
    @3
    vj
    @24
    wph
    @18
    @15
    vj
    wph
    vj
    nfv
    @18
    vj
    nfv
    @14
    vj
    cZ
    nfra1
    nf3an
    @19
    @1
    @24
    wcel
    #
    @3
    @19
    @33
    wa
    #
    @13
    @3
    wph
    @18
    @33
    @13
    @15
    @26
    @33
    wa
    #
    @12
    @22
    @1
    wph
    @18
    @33
    simplr
    @26
    @22
    cr
    wcel
    @33
    @26
    cZ
    cr
    @22
    @11
    @32
    sseldi
    #
    adantr
    #
    @33
    @1
    cr
    wcel
    @26
    @22
    @1
    eluzelre
    adantl
    #
    @26
    @12
    @22
    cle
    wbr
    @33
    @26
    @12
    @20
    @22
    wph
    @18
    simpr
    @18
    @20
    cr
    wcel
    #
    wph
    @18
    @20
    @29
    zred
    #
    adantl
    #
    @36
    @18
    @12
    @20
    cle
    wbr
    wph
    @12
    ceilge
    adantl
    @26
    cM
    cr
    wcel
    #
    @39
    @20
    @22
    cle
    wbr
    wph
    @42
    @18
    wph
    cZ
    cr
    cM
    @11
    @31
    sseldi
    #
    adantr
    #
    @41
    cM
    @20
    max2
    syl2anc
    letrd
    adantr
    @33
    @22
    @1
    cle
    wbr
    @26
    @22
    @1
    eluzle
    adantl
    #
    letrd
    3adantl3
    @34
    @15
    @1
    cZ
    wcel
    #
    @14
    wph
    @18
    @15
    @33
    simpl3
    wph
    @18
    @33
    @46
    @15
    @35
    cM
    @1
    cZ
    limsupmnfuzlem.2
    wph
    @28
    @18
    @33
    limsupmnfuzlem.1
    ad2antrr
    @33
    @1
    cz
    wcel
    #
    @26
    @22
    @1
    eluzelz
    adantl
    @35
    cM
    @22
    @1
    @26
    @42
    @33
    @44
    adantr
    @37
    @38
    @26
    cM
    @22
    cle
    wbr
    #
    @33
    wph
    @42
    @39
    @48
    @18
    @43
    @40
    cM
    @20
    max1
    syl2an
    adantr
    @45
    letrd
    eluzd
    3adantl3
    @14
    vj
    cZ
    rspa
    syl2anc
    mpd
    ex
    ralrimi
    @8
    @25
    vk
    @22
    cZ
    @0
    @22
    wceq
    @3
    vj
    @7
    @24
    @0
    @22
    cuz
    fveq2
    raleqdv
    rspcev
    syl2anc
    3exp
    rexlimdv
    imp
    sylan2
    ex
    wph
    @9
    @6
    @9
    wph
    @0
    cZ
    wcel
    #
    @8
    wa
    #
    vk
    cr
    wrex
    #
    @6
    @9
    @51
    @10
    @9
    @51
    wb
    @11
    @8
    vk
    cZ
    cr
    rexss
    ax-mp
    biimpi
    wph
    @51
    @6
    wph
    @50
    @5
    vk
    cr
    @50
    @5
    wi
    wph
    @50
    @4
    vj
    cZ
    @49
    @8
    vj
    @49
    vj
    nfv
    @3
    vj
    @7
    nfra1
    nfan
    @50
    @46
    @2
    @3
    @50
    @46
    @2
    w3a
    @8
    @1
    @7
    wcel
    #
    @3
    @49
    @8
    @46
    @2
    simp1r
    @49
    @46
    @2
    @52
    @8
    @49
    @46
    @2
    w3a
    @0
    @1
    @7
    @7
    eqid
    @49
    @46
    @0
    cz
    wcel
    @2
    cM
    @0
    cZ
    limsupmnfuzlem.2
    eluzelz2
    3ad2ant1
    @46
    @49
    @47
    @2
    cM
    @1
    cZ
    limsupmnfuzlem.2
    eluzelz2
    3ad2ant2
    @49
    @46
    @2
    simp3
    eluzd
    3adant1r
    @3
    vj
    @7
    rspa
    syl2anc
    3exp
    ralrimi
    a1i
    reximdv
    imp
    sylan2
    ex
    impbid
    ralbidv
    bitrd
end
