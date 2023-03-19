include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cixp.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "wfn.mm"
include "wb.mm"
include "cfn.mm"
include "ralrimiva.mm"
include "prdsbas3.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ixpfn.mm"
include "vex.mm"
include "elixp.mm"
include "baib.mm"
include "3syl.mm"
include "cxmt.mm"
include "cxr.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "prdsbascl.mm"
include "adantr.mm"
include "r19.21bi.mm"
include "simpr.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "ralbidva.mm"
include "cmpt.mm"
include "crn.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "breq1.mm"
include "ralrnmpt.mm"
include "syl.mm"
include "cc0.mm"
include "csn.mm"
include "c0ex.mm"
include "ralsn.mm"
include "sylibr.mm"
include "cun.mm"
include "ralunb.mm"
include "wi.mm"
include "csup.mm"
include "prdsdsval3.mm"
include "wor.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "xrltso.mm"
include "a1i.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "abrexfi.mm"
include "syl5eqel.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssun2.mm"
include "snss.mm"
include "mpbir.mm"
include "ne0i.mm"
include "mp1i.mm"
include "wf.mm"
include "fmptd.mm"
include "frn.mm"
include "0xr.mm"
include "snssd.mm"
include "unssd.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "eqeltrd.mm"
include "rspcv.mm"
include "syl5bir.mm"
include "mpan2d.mm"
include "sylbird.mm"
include "cle.mm"
include "ssun1.mm"
include "ovex.mm"
include "elabrex.mm"
include "adantl.mm"
include "syl6eleqr.mm"
include "sseldi.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "prdsxmet.mm"
include "xrlelttr.mm"
include "mpand.mm"
include "ralrimdva.mm"
include "impbid.mm"
include "3bitrrd.mm"
include "pm5.32da.mm"
include "elbl.mm"
include "blssm.mm"
include "ss2ixp.mm"
include "sseqtr4d.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem prdsbl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cE: class E
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vz: setvar z
  let vy: setvar y
  assume prdsbl.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsbl.b: |- B = ( Base ` Y )
  assume prdsbl.v: |- V = ( Base ` R )
  assume prdsbl.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume prdsbl.d: |- D = ( dist ` Y )
  assume prdsbl.s: |- ( ph -> S e. W )
  assume prdsbl.i: |- ( ph -> I e. Fin )
  assume prdsbl.r: |- ( ( ph /\ x e. I ) -> R e. Z )
  assume prdsbl.m: |- ( ( ph /\ x e. I ) -> E e. ( *Met ` V ) )
  assume prdsbl.p: |- ( ph -> P e. B )
  assume prdsbl.a: |- ( ph -> A e. RR* )
  assume prdsbl.g: |- ( ph -> 0 < A )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint I x
  disjoint P x
  disjoint ph x
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint x z
  disjoint A z
  disjoint x y
  disjoint B y
  disjoint D f
  disjoint D z
  disjoint f y
  disjoint I f
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P f
  disjoint P y
  disjoint P z
  disjoint E f
  disjoint E y
  disjoint E z
  disjoint f ph
  disjoint ph y
  disjoint R y
  disjoint R z
  disjoint S y
  disjoint W y
  disjoint Y y
  assert |- ( ph -> ( P ( ball ` D ) A ) = X_ x e. I ( ( P ` x ) ( ball ` E ) A ) )

  proof
    wph
    vf
    cP
    cA
    cD
    cbl
    cfv
    co
    #
    vx
    cI
    vx
    cv
    #
    cP
    cfv
    #
    cA
    cE
    cbl
    cfv
    co
    #
    cixp
    #
    wph
    vf
    cv
    #
    cB
    wcel
    #
    cP
    @5
    cD
    co
    #
    cA
    clt
    wbr
    #
    wa
    #
    @6
    @5
    @4
    wcel
    #
    wa
    @5
    @0
    wcel
    #
    @10
    wph
    @6
    @8
    @10
    wph
    @6
    wa
    #
    @10
    @1
    @5
    cfv
    #
    @3
    wcel
    #
    vx
    cI
    wral
    #
    @2
    @13
    cE
    co
    #
    cA
    clt
    wbr
    #
    vx
    cI
    wral
    #
    @8
    @12
    @5
    vx
    cI
    cV
    cixp
    #
    wcel
    #
    @5
    cI
    wfn
    #
    @10
    @15
    wb
    wph
    @6
    @20
    wph
    cB
    @19
    @5
    wph
    vx
    cB
    cR
    cS
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsbl.y
    prdsbl.b
    prdsbl.s
    prdsbl.i
    wph
    cR
    cZ
    wcel
    #
    vx
    cI
    prdsbl.r
    ralrimiva
    #
    prdsbl.v
    prdsbas3
    #
    eleq2d
    biimpa
    vx
    cI
    cV
    @5
    ixpfn
    @10
    @21
    @15
    vx
    cI
    @3
    @5
    vf
    vex
    elixp
    baib
    3syl
    @12
    @14
    @17
    vx
    cI
    @12
    @1
    cI
    wcel
    #
    wa
    #
    cE
    cV
    cxmt
    cfv
    wcel
    #
    cA
    cxr
    wcel
    #
    @2
    cV
    wcel
    #
    @13
    cV
    wcel
    #
    @14
    @17
    wb
    wph
    @25
    @27
    @6
    prdsbl.m
    adantlr
    #
    wph
    @28
    @6
    @25
    prdsbl.a
    ad2antrr
    #
    @12
    @29
    vx
    cI
    wph
    @29
    vx
    cI
    wral
    @6
    wph
    vx
    cB
    cR
    cS
    cP
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsbl.y
    prdsbl.b
    prdsbl.s
    prdsbl.i
    @23
    prdsbl.v
    prdsbl.p
    prdsbascl
    #
    adantr
    r19.21bi
    #
    @12
    @30
    vx
    cI
    @12
    vx
    cB
    cR
    cS
    @5
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsbl.y
    prdsbl.b
    wph
    cS
    cW
    wcel
    @6
    prdsbl.s
    adantr
    #
    wph
    cI
    cfn
    wcel
    #
    @6
    prdsbl.i
    adantr
    #
    wph
    @22
    vx
    cI
    wral
    @6
    @23
    adantr
    #
    prdsbl.v
    wph
    @6
    simpr
    #
    prdsbascl
    r19.21bi
    #
    @13
    cE
    @2
    cA
    cV
    elbl2
    syl22anc
    ralbidva
    @12
    @18
    @8
    @12
    @18
    vz
    cv
    #
    cA
    clt
    wbr
    #
    vz
    vx
    cI
    @16
    cmpt
    #
    crn
    #
    wral
    #
    @8
    @12
    @16
    cxr
    wcel
    #
    vx
    cI
    wral
    @45
    @18
    wb
    @12
    @46
    vx
    cI
    @26
    @27
    @29
    @30
    @46
    @31
    @34
    @40
    @2
    @13
    cE
    cV
    xmetcl
    syl3anc
    #
    ralrimiva
    @42
    @17
    vx
    vz
    cI
    @16
    @43
    cxr
    @43
    eqid
    #
    @41
    @16
    cA
    clt
    breq1
    ralrnmpt
    syl
    @12
    @45
    @42
    vz
    cc0
    csn
    #
    wral
    #
    @8
    @12
    cc0
    cA
    clt
    wbr
    #
    @50
    wph
    @51
    @6
    prdsbl.g
    adantr
    @42
    @51
    vz
    cc0
    c0ex
    @41
    cc0
    cA
    clt
    breq1
    ralsn
    sylibr
    @45
    @50
    wa
    @42
    vz
    @44
    @49
    cun
    #
    wral
    #
    @12
    @8
    @42
    vz
    @44
    @49
    ralunb
    @12
    @7
    @52
    wcel
    @53
    @8
    wi
    @12
    @7
    @52
    cxr
    clt
    csup
    #
    @52
    @12
    vx
    cB
    cD
    cR
    cS
    cE
    cP
    @5
    cI
    cV
    cW
    cfn
    cZ
    cY
    prdsbl.y
    prdsbl.b
    @35
    @37
    @38
    wph
    cP
    cB
    wcel
    #
    @6
    prdsbl.p
    adantr
    @39
    prdsbl.v
    prdsbl.e
    prdsbl.d
    prdsdsval3
    #
    @12
    cxr
    clt
    wor
    #
    @52
    cfn
    wcel
    #
    @52
    c0
    wne
    #
    @52
    cxr
    wss
    #
    @54
    @52
    wcel
    @57
    @12
    xrltso
    a1i
    @12
    @44
    cfn
    wcel
    #
    @49
    cfn
    wcel
    @58
    @12
    @36
    @61
    @37
    @36
    @44
    vy
    cv
    @16
    wceq
    vx
    cI
    wrex
    vy
    cab
    #
    cfn
    vx
    vy
    cI
    @16
    @43
    @48
    rnmpt
    #
    vx
    vy
    cI
    @16
    abrexfi
    syl5eqel
    syl
    cc0
    snfi
    @44
    @49
    unfi
    sylancl
    cc0
    @52
    wcel
    #
    @59
    @12
    @64
    @49
    @52
    wss
    @49
    @44
    ssun2
    cc0
    @52
    c0ex
    snss
    mpbir
    @52
    cc0
    ne0i
    mp1i
    @12
    @44
    @49
    cxr
    @12
    cI
    cxr
    @43
    wf
    @44
    cxr
    wss
    @12
    vx
    cI
    @16
    cxr
    @43
    @47
    @48
    fmptd
    cI
    cxr
    @43
    frn
    syl
    @12
    cc0
    cxr
    cc0
    cxr
    wcel
    @12
    0xr
    a1i
    snssd
    unssd
    #
    cxr
    @52
    clt
    fisupcl
    syl13anc
    eqeltrd
    @42
    @8
    vz
    @7
    @52
    @41
    @7
    cA
    clt
    breq1
    rspcv
    syl
    syl5bir
    mpan2d
    sylbird
    @12
    @8
    @17
    vx
    cI
    @26
    @16
    @7
    cle
    wbr
    #
    @8
    @17
    @26
    @16
    @54
    @7
    cle
    @26
    @60
    @16
    @52
    wcel
    @16
    @54
    cle
    wbr
    @12
    @60
    @25
    @65
    adantr
    @26
    @44
    @52
    @16
    @44
    @49
    ssun1
    @26
    @16
    @62
    @44
    @25
    @16
    @62
    wcel
    @12
    vx
    vy
    cI
    @16
    @2
    @13
    cE
    ovex
    elabrex
    adantl
    @63
    syl6eleqr
    sseldi
    @52
    @16
    supxrub
    syl2anc
    @12
    @7
    @54
    wceq
    @25
    @56
    adantr
    breqtrrd
    @26
    @46
    @7
    cxr
    wcel
    #
    @28
    @66
    @8
    wa
    @17
    wi
    @47
    @26
    cD
    cB
    cxmt
    cfv
    wcel
    #
    @55
    @6
    @67
    wph
    @68
    @6
    @25
    wph
    vx
    cB
    cD
    cR
    cS
    cE
    cI
    cV
    cW
    cfn
    cY
    cZ
    prdsbl.y
    prdsbl.b
    prdsbl.v
    prdsbl.e
    prdsbl.d
    prdsbl.s
    prdsbl.i
    prdsbl.r
    prdsbl.m
    prdsxmet
    #
    ad2antrr
    wph
    @55
    @6
    @25
    prdsbl.p
    ad2antrr
    @12
    @6
    @25
    @39
    adantr
    cP
    @5
    cD
    cB
    xmetcl
    syl3anc
    @32
    @16
    @7
    cA
    xrlelttr
    syl3anc
    mpand
    ralrimdva
    impbid
    3bitrrd
    pm5.32da
    wph
    @68
    @55
    @28
    @11
    @9
    wb
    @69
    prdsbl.p
    prdsbl.a
    @5
    cD
    cP
    cA
    cB
    elbl
    syl3anc
    wph
    @10
    @6
    wph
    @4
    cB
    @5
    wph
    @4
    @19
    cB
    wph
    @3
    cV
    wss
    #
    vx
    cI
    wral
    @4
    @19
    wss
    wph
    @70
    vx
    cI
    wph
    @25
    wa
    @27
    @29
    @28
    @70
    prdsbl.m
    wph
    @29
    vx
    cI
    @33
    r19.21bi
    wph
    @28
    @25
    prdsbl.a
    adantr
    cE
    @2
    cA
    cV
    blssm
    syl3anc
    ralrimiva
    vx
    cI
    @3
    cV
    ss2ixp
    syl
    @24
    sseqtr4d
    sseld
    pm4.71rd
    3bitr4d
    eqrdv
end
