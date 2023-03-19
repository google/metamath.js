include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "sprsymrelf.mm"
include "a1i.mm"
include "wa.mm"
include "cpr.mm"
include "copab.mm"
include "cxp.mm"
include "cpw.mm"
include "wbr.mm"
include "wb.mm"
include "wi.mm"
include "breq.mm"
include "bibi12d.mm"
include "2ralbidv.mm"
include "elrab2.mm"
include "cspr.mm"
include "crab.mm"
include "eqid.mm"
include "sprsymrelfolem1.mm"
include "eleqtrri.mm"
include "rexeq.mm"
include "opabbidv.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "wss.mm"
include "selpw.mm"
include "wrel.mm"
include "cvv.mm"
include "xpss.mm"
include "sstr2.mm"
include "mpi.mm"
include "df-rel.mm"
include "sylibr.mm"
include "dfrel4v.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfra2.mm"
include "sprsymrelfolem2.mm"
include "3expa.mm"
include "opabbid.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "syl5bi.mm"
include "mpd.mm"
include "expcom.mm"
include "sylbi.mm"
include "imp31.mm"
include "rspcedvd.mm"
include "impcom.mm"
include "sprsymrelfv.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem sprsymrelfo
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vp: setvar p
  let vc: setvar c
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vq: setvar q
  let vt: setvar t
  let vk: setvar k
  assume sprsymrelf.p: |- P = ~P ( Pairs ` V )
  assume sprsymrelf.r: |- R = { r e. ~P ( V X. V ) | A. x e. V A. y e. V ( x r y <-> y r x ) }
  assume sprsymrelf.f: |- F = ( p e. P |-> { <. x , y >. | E. c e. p c = { x , y } } )

  disjoint c p
  disjoint c x
  disjoint c y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint p r
  disjoint R p
  disjoint V c
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint c r
  disjoint r x
  disjoint r y
  disjoint W c
  disjoint W x
  disjoint W y
  disjoint P p
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint c p
  disjoint p x
  disjoint p y
  disjoint X c
  disjoint X p
  disjoint X x
  disjoint X y
  disjoint a b
  disjoint a c
  disjoint a p
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b p
  disjoint b x
  disjoint b y
  disjoint F a
  disjoint F b
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint a f
  disjoint a q
  disjoint a t
  disjoint b f
  disjoint b q
  disjoint b t
  disjoint c f
  disjoint c q
  disjoint c t
  disjoint f q
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint t x
  disjoint t y
  disjoint r t
  disjoint F f
  disjoint F t
  disjoint P f
  disjoint P t
  disjoint R f
  disjoint f p
  disjoint R t
  disjoint V f
  disjoint V q
  disjoint V t
  disjoint W a
  disjoint W b
  disjoint W f
  disjoint W t
  disjoint k x
  assert |- ( V e. W -> F : P -onto-> R )

  proof
    cV
    cW
    wcel
    #
    cP
    cR
    cF
    wf
    #
    vt
    cv
    #
    vf
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vf
    cP
    wrex
    #
    vt
    cR
    wral
    cP
    cR
    cF
    wfo
    @1
    @0
    vx
    vy
    cP
    cR
    cF
    cV
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    sprsymrelf.f
    sprsymrelf
    a1i
    @0
    @6
    vt
    cR
    @0
    @2
    cR
    wcel
    #
    wa
    #
    @6
    @2
    vc
    cv
    vx
    cv
    #
    vy
    cv
    #
    cpr
    wceq
    #
    vc
    @3
    wrex
    #
    vx
    vy
    copab
    #
    wceq
    #
    vf
    cP
    wrex
    #
    @7
    @0
    @15
    @7
    @2
    cV
    cV
    cxp
    #
    cpw
    #
    wcel
    #
    @9
    @10
    @2
    wbr
    #
    @10
    @9
    @2
    wbr
    #
    wb
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    #
    wa
    #
    @0
    @15
    wi
    @9
    @10
    vr
    cv
    #
    wbr
    #
    @10
    @9
    @25
    wbr
    #
    wb
    #
    vy
    cV
    wral
    vx
    cV
    wral
    @23
    vr
    @2
    @17
    cR
    @25
    @2
    wceq
    #
    @28
    @21
    vx
    vy
    cV
    cV
    @29
    @26
    @19
    @27
    @20
    @9
    @10
    @25
    @2
    breq
    @10
    @9
    @25
    @2
    breq
    bibi12d
    2ralbidv
    sprsymrelf.r
    elrab2
    @24
    @0
    @15
    @24
    @0
    wa
    #
    @14
    @2
    @11
    vc
    vq
    cv
    va
    cv
    #
    vb
    cv
    #
    cpr
    wceq
    @31
    @32
    @2
    wbr
    wi
    vb
    cV
    wral
    va
    cV
    wral
    vq
    cV
    cspr
    cfv
    #
    crab
    #
    wrex
    #
    vx
    vy
    copab
    #
    wceq
    #
    vf
    @34
    cP
    @34
    cP
    wcel
    @30
    @34
    @33
    cpw
    cP
    @34
    @2
    cV
    vq
    va
    vb
    @34
    eqid
    #
    sprsymrelfolem1
    sprsymrelf.p
    eleqtrri
    a1i
    @3
    @34
    wceq
    #
    @14
    @37
    wb
    @30
    @39
    @13
    @36
    @2
    @39
    @12
    @35
    vx
    vy
    @11
    vc
    @3
    @34
    rexeq
    opabbidv
    eqeq2d
    adantl
    @18
    @23
    @0
    @37
    @18
    @2
    @16
    wss
    #
    @23
    @0
    @37
    wi
    wi
    vt
    @16
    selpw
    @40
    @0
    @23
    @37
    @0
    @40
    @23
    @37
    wi
    #
    @0
    @40
    wa
    #
    @2
    wrel
    #
    @41
    @40
    @43
    @0
    @40
    @2
    cvv
    cvv
    cxp
    #
    wss
    #
    @43
    @40
    @16
    @44
    wss
    @45
    cV
    cV
    xpss
    @2
    @16
    @44
    sstr2
    mpi
    @2
    df-rel
    sylibr
    adantl
    @43
    @2
    @19
    vx
    vy
    copab
    #
    wceq
    #
    @42
    @41
    vx
    vy
    @2
    dfrel4v
    @42
    @23
    @47
    @37
    @42
    @23
    @47
    @37
    wi
    @42
    @23
    wa
    #
    @47
    @37
    @48
    @46
    @36
    @2
    @48
    @19
    @35
    vx
    vy
    @42
    @23
    vx
    @42
    vx
    nfv
    @22
    vx
    cV
    nfra1
    nfan
    @42
    @23
    vy
    @42
    vy
    nfv
    @21
    vx
    vy
    cV
    cV
    nfra2
    nfan
    @0
    @40
    @23
    @19
    @35
    wb
    vx
    vy
    @34
    @2
    cV
    cW
    vq
    va
    vb
    vc
    @38
    sprsymrelfolem2
    3expa
    opabbid
    eqeq2d
    biimpd
    ex
    com23
    syl5bi
    mpd
    expcom
    com23
    sylbi
    imp31
    rspcedvd
    ex
    sylbi
    impcom
    @8
    @5
    @14
    vf
    cP
    @8
    @3
    cP
    wcel
    #
    wa
    @4
    @13
    @2
    @49
    @4
    @13
    wceq
    @8
    vx
    vy
    cP
    cR
    cF
    cV
    @3
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    sprsymrelf.f
    sprsymrelfv
    adantl
    eqeq2d
    rexbidva
    mpbird
    ralrimiva
    vf
    vt
    cP
    cR
    cF
    dffo3
    sylanbrc
end
