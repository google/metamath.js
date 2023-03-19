include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "wb.mm"
include "fovrnda.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "biantrud.mm"
include "3bitr2d.mm"
include "w3a.mm"
include "cr.mm"
include "cxad.mm"
include "cpnf.mm"
include "cmnf.mm"
include "caddc.mm"
include "3expa.mm"
include "rexadd.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "anassrs.mm"
include "3adantr3.mm"
include "pnfge.mm"
include "syl.mm"
include "ad2antrr.mm"
include "oveq2.mm"
include "wne.mm"
include "cicc.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "wral.mm"
include "ffn.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "adantr.mm"
include "simpr3.mm"
include "simpr1.mm"
include "fovrnd.mm"
include "simplbi.mm"
include "renemnf.mm"
include "xaddpnf1.mm"
include "syl2an.mm"
include "sylan9eqr.mm"
include "wi.mm"
include "wn.mm"
include "simpr2.mm"
include "simprbi.mm"
include "ge0nemnf.mm"
include "syl2anc.mm"
include "a1d.mm"
include "necon4bd.mm"
include "imp.mm"
include "w3o.mm"
include "elxr.mm"
include "sylib.mm"
include "mpjao3dan.mm"
include "oveq1.mm"
include "xaddpnf2.mm"
include "isxmetd.mm"

theorem isxmet2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cX: class X
  assume isxmetd.0: |- ( ph -> X e. _V )
  assume isxmetd.1: |- ( ph -> D : ( X X. X ) --> RR* )
  assume isxmet2d.2: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> 0 <_ ( x D y ) )
  assume isxmet2d.3: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( ( x D y ) <_ 0 <-> x = y ) )
  assume isxmet2d.4: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) /\ ( ( z D x ) e. RR /\ ( z D y ) e. RR ) ) -> ( x D y ) <_ ( ( z D x ) + ( z D y ) ) )

  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> D e. ( *Met ` X ) )

  proof
    wph
    vx
    vy
    vz
    cD
    cX
    isxmetd.0
    isxmetd.1
    wph
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    wa
    wa
    #
    @0
    @2
    cD
    co
    #
    cc0
    wceq
    #
    @5
    cc0
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    @7
    @0
    @2
    wceq
    @4
    @5
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    @6
    @9
    wb
    wph
    @0
    @2
    cxr
    cX
    cX
    cD
    isxmetd.1
    fovrnda
    #
    0xr
    @5
    cc0
    xrletri3
    sylancl
    @4
    @8
    @7
    isxmet2d.2
    biantrud
    isxmet2d.3
    3bitr2d
    wph
    @1
    @3
    vz
    cv
    #
    cX
    wcel
    #
    w3a
    #
    wa
    #
    @12
    @0
    cD
    co
    #
    cr
    wcel
    #
    @5
    @16
    @12
    @2
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    @16
    cpnf
    wceq
    #
    @16
    cmnf
    wceq
    #
    @15
    @17
    wa
    #
    @18
    cr
    wcel
    #
    @20
    @18
    cpnf
    wceq
    #
    @18
    cmnf
    wceq
    #
    @15
    @17
    @24
    @20
    @15
    @17
    @24
    wa
    #
    wa
    @5
    @16
    @18
    caddc
    co
    #
    @19
    cle
    wph
    @14
    @27
    @5
    @28
    cle
    wbr
    isxmet2d.4
    3expa
    @27
    @19
    @28
    wceq
    @15
    @16
    @18
    rexadd
    adantl
    breqtrrd
    anassrs
    @23
    @25
    wa
    @5
    cpnf
    @19
    cle
    @15
    @5
    cpnf
    cle
    wbr
    #
    @17
    @25
    @15
    @10
    @29
    wph
    @1
    @3
    @10
    @13
    @11
    3adantr3
    @5
    pnfge
    syl
    #
    ad2antrr
    @25
    @23
    @19
    @16
    cpnf
    cxad
    co
    #
    cpnf
    @18
    cpnf
    @16
    cxad
    oveq2
    @15
    @16
    cxr
    wcel
    #
    @16
    cmnf
    wne
    #
    @31
    cpnf
    wceq
    @17
    @15
    @16
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @32
    @15
    @12
    @0
    @34
    cX
    cX
    cD
    wph
    cX
    cX
    cxp
    #
    @34
    cD
    wf
    #
    @14
    wph
    cD
    @36
    wfn
    #
    @5
    @34
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @37
    wph
    @36
    cxr
    cD
    wf
    @38
    isxmetd.1
    @36
    cxr
    cD
    ffn
    syl
    wph
    @39
    vx
    vy
    cX
    cX
    @4
    @10
    @8
    @39
    @11
    isxmet2d.2
    @5
    elxrge0
    sylanbrc
    ralrimivva
    vx
    vy
    cX
    cX
    @34
    cD
    ffnov
    sylanbrc
    adantr
    #
    wph
    @1
    @3
    @13
    simpr3
    #
    wph
    @1
    @3
    @13
    simpr1
    fovrnd
    #
    @35
    @32
    cc0
    @16
    cle
    wbr
    #
    @16
    elxrge0
    #
    simplbi
    syl
    #
    @16
    renemnf
    @16
    xaddpnf1
    syl2an
    sylan9eqr
    breqtrrd
    @23
    @26
    @20
    @15
    @26
    @20
    wi
    @17
    @15
    @20
    @18
    cmnf
    @15
    @18
    cmnf
    wne
    #
    @20
    wn
    #
    @15
    @18
    cxr
    wcel
    #
    cc0
    @18
    cle
    wbr
    #
    @46
    @15
    @18
    @34
    wcel
    #
    @48
    @15
    @12
    @2
    @34
    cX
    cX
    cD
    @40
    @41
    wph
    @1
    @3
    @13
    simpr2
    fovrnd
    #
    @50
    @48
    @49
    @18
    elxrge0
    #
    simplbi
    syl
    #
    @15
    @50
    @49
    @51
    @50
    @48
    @49
    @52
    simprbi
    syl
    @18
    ge0nemnf
    syl2anc
    #
    a1d
    necon4bd
    adantr
    imp
    @23
    @48
    @24
    @25
    @26
    w3o
    @15
    @48
    @17
    @53
    adantr
    @18
    elxr
    sylib
    mpjao3dan
    @15
    @21
    wa
    @5
    cpnf
    @19
    cle
    @15
    @29
    @21
    @30
    adantr
    @21
    @15
    @19
    cpnf
    @18
    cxad
    co
    #
    cpnf
    @16
    cpnf
    @18
    cxad
    oveq1
    @15
    @48
    @46
    @55
    cpnf
    wceq
    @53
    @54
    @18
    xaddpnf2
    syl2anc
    sylan9eqr
    breqtrrd
    @15
    @22
    @20
    @15
    @20
    @16
    cmnf
    @15
    @33
    @47
    @15
    @32
    @43
    @33
    @45
    @15
    @35
    @43
    @42
    @35
    @32
    @43
    @44
    simprbi
    syl
    @16
    ge0nemnf
    syl2anc
    a1d
    necon4bd
    imp
    @15
    @32
    @17
    @21
    @22
    w3o
    @45
    @16
    elxr
    sylib
    mpjao3dan
    isxmetd
end
