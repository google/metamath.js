include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "simpr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "cxr.mm"
include "cmnf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "sseldi.mm"
include "adantr.mm"
include "abscld.mm"
include "w3a.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "sylib.mm"
include "simp2d.mm"
include "ge0gtmnf.mm"
include "syl2anc.mm"
include "wi.mm"
include "ressxr.mm"
include "xrltle.mm"
include "mpd.mm"
include "xrre.mm"
include "syl22anc.mm"
include "avglt1.mm"
include "mpbid.mm"
include "cv.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "crab.mm"
include "csup.mm"
include "wss.mm"
include "ssrab2.mm"
include "sstri.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "cn0.mm"
include "cc.mm"
include "wf.mm"
include "recnd.mm"
include "0red.mm"
include "lelttrd.mm"
include "ltled.mm"
include "absidd.mm"
include "avglt2.mm"
include "eqbrtrd.mm"
include "radcnvlem3.mm"
include "wceq.mm"
include "fveq2.mm"
include "seqeq3d.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "supxrub.mm"
include "sylancr.mm"
include "syl6breqr.mm"
include "lenltd.mm"
include "pm2.65da.mm"
include "xrlenlt.mm"
include "mpbird.mm"

theorem radcnvle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vr: setvar r
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let cN: class N
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume radcnv.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume radcnvle.x: |- ( ph -> X e. CC )
  assume radcnvle.a: |- ( ph -> seq 0 ( + , ( G ` X ) ) e. dom ~~> )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint G r
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H m
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint G m
  disjoint r s
  disjoint r y
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( ph -> ( abs ` X ) <_ R )

  proof
    wph
    cX
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    cR
    @0
    clt
    wbr
    #
    wn
    #
    wph
    @2
    cR
    cR
    @0
    caddc
    co
    #
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    wph
    @2
    wa
    #
    @2
    @6
    wph
    @2
    simpr
    #
    @7
    cR
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @2
    @6
    wb
    @7
    cR
    cxr
    wcel
    #
    @10
    cmnf
    cR
    clt
    wbr
    #
    cR
    @0
    cle
    wbr
    #
    @9
    wph
    @11
    @2
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cR
    cc0
    cpnf
    iccssxr
    wph
    vx
    cA
    cR
    vn
    cG
    vr
    pser.g
    radcnv.a
    radcnv.r
    radcnvcl
    #
    sseldi
    #
    adantr
    #
    wph
    @10
    @2
    wph
    cX
    radcnvle.x
    abscld
    #
    adantr
    #
    wph
    @12
    @2
    wph
    @11
    cc0
    cR
    cle
    wbr
    #
    @12
    @16
    wph
    @11
    @20
    cR
    cpnf
    cle
    wbr
    #
    wph
    cR
    @14
    wcel
    #
    @11
    @20
    @21
    w3a
    #
    @15
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @22
    @23
    wb
    0xr
    pnfxr
    cc0
    cpnf
    cR
    elicc1
    mp2an
    sylib
    simp2d
    #
    cR
    ge0gtmnf
    syl2anc
    adantr
    @7
    @2
    @13
    @8
    @7
    @11
    @0
    cxr
    wcel
    #
    @2
    @13
    wi
    @17
    wph
    @25
    @2
    wph
    cr
    cxr
    @0
    ressxr
    @18
    sseldi
    #
    adantr
    cR
    @0
    xrltle
    syl2anc
    mpd
    cR
    @0
    xrre
    syl22anc
    #
    @19
    cR
    @0
    avglt1
    syl2anc
    mpbid
    #
    @7
    @5
    cR
    cle
    wbr
    @6
    wn
    @7
    @5
    caddc
    vr
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    cR
    cle
    @7
    @34
    cxr
    wss
    @5
    @34
    wcel
    #
    @5
    @35
    cle
    wbr
    @34
    cr
    cxr
    @33
    vr
    cr
    ssrab2
    ressxr
    sstri
    @7
    @5
    cr
    wcel
    caddc
    @5
    cG
    cfv
    #
    cc0
    cseq
    #
    @32
    wcel
    #
    @36
    @7
    @4
    @7
    cR
    @0
    @27
    @19
    readdcld
    rehalfcld
    #
    @7
    vx
    cA
    vn
    cG
    @5
    cX
    pser.g
    wph
    cn0
    cc
    cA
    wf
    @2
    radcnv.a
    adantr
    @7
    @5
    @40
    recnd
    wph
    cX
    cc
    wcel
    @2
    radcnvle.x
    adantr
    @7
    @5
    cabs
    cfv
    @5
    @0
    clt
    @7
    @5
    @40
    @7
    cc0
    @5
    @7
    0red
    #
    @40
    @7
    cc0
    cR
    @5
    @41
    @27
    @40
    wph
    @20
    @2
    @24
    adantr
    @28
    lelttrd
    ltled
    absidd
    @7
    @2
    @5
    @0
    clt
    wbr
    #
    @8
    @7
    @9
    @10
    @2
    @42
    wb
    @27
    @19
    cR
    @0
    avglt2
    syl2anc
    mpbid
    eqbrtrd
    wph
    caddc
    cX
    cG
    cfv
    cc0
    cseq
    @32
    wcel
    @2
    radcnvle.a
    adantr
    radcnvlem3
    caddc
    vy
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    @32
    wcel
    #
    @39
    vy
    @5
    cr
    @34
    @43
    @5
    wceq
    #
    @45
    @38
    @32
    @47
    @44
    @37
    caddc
    cc0
    @43
    @5
    cG
    fveq2
    seqeq3d
    eleq1d
    @33
    @46
    vr
    vy
    cr
    @29
    @43
    wceq
    #
    @31
    @45
    @32
    @48
    @30
    @44
    caddc
    cc0
    @29
    @43
    cG
    fveq2
    seqeq3d
    eleq1d
    cbvrabv
    elrab2
    sylanbrc
    @34
    @5
    supxrub
    sylancr
    radcnv.r
    syl6breqr
    @7
    @5
    cR
    @40
    @27
    lenltd
    mpbid
    pm2.65da
    wph
    @25
    @11
    @1
    @3
    wb
    @26
    @16
    @0
    cR
    xrlenlt
    syl2anc
    mpbird
end
