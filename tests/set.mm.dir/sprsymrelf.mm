include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "wcel.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "cspr.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "sprsymrelfvlem.mm"
include "wel.mm"
include "prcom.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "cop.mm"
include "df-br.mm"
include "opabid.mm"
include "bitri.mm"
include "vex.mm"
include "weq.mm"
include "preq12.mm"
include "rexbidv.mm"
include "cbvopabv.mm"
include "braba.mm"
include "3bitr4g.mm"
include "ralrimivva.mm"
include "jca.mm"
include "eleq2i.mm"
include "elpw.mm"
include "nfopab1.mm"
include "nfeq2.mm"
include "nfopab2.mm"
include "breq.mm"
include "bibi12d.mm"
include "ralbid.mm"
include "elrab.mm"
include "3imtr4i.mm"
include "syl6eleqr.mm"
include "fmpti.mm"

theorem sprsymrelf
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cF: class F
  let cV: class V
  let vr: setvar r
  let vp: setvar p
  let vc: setvar c
  let cX: class X
  let va: setvar a
  let vb: setvar b
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
  disjoint k x
  assert |- F : P --> R

  proof
    vp
    cP
    cR
    vc
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vc
    vp
    cv
    #
    wrex
    #
    vx
    vy
    copab
    #
    cF
    sprsymrelf.f
    @5
    cP
    wcel
    #
    @7
    @1
    @2
    vr
    cv
    #
    wbr
    #
    @2
    @1
    @9
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
    vr
    cV
    cV
    cxp
    cpw
    #
    crab
    #
    cR
    @5
    cV
    cspr
    cfv
    #
    wss
    #
    @7
    @15
    wcel
    #
    @1
    @2
    @7
    wbr
    #
    @2
    @1
    @7
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
    @8
    @7
    @16
    wcel
    @18
    @19
    @24
    vx
    vy
    @5
    cV
    vc
    sprsymrelfvlem
    @18
    @22
    vx
    vy
    cV
    cV
    @18
    @1
    cV
    wcel
    @2
    cV
    wcel
    wa
    wa
    #
    @6
    @0
    @2
    @1
    cpr
    #
    wceq
    #
    vc
    @5
    wrex
    #
    @20
    @21
    @25
    @4
    @27
    vc
    @5
    @25
    vc
    vp
    wel
    wa
    #
    @3
    @26
    @0
    @3
    @26
    wceq
    @29
    @1
    @2
    prcom
    a1i
    eqeq2d
    rexbidva
    @20
    @1
    @2
    cop
    @7
    wcel
    @6
    @1
    @2
    @7
    df-br
    @6
    vx
    vy
    opabid
    bitri
    @0
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vc
    @5
    wrex
    #
    @28
    va
    vb
    @2
    @1
    @7
    vy
    vex
    vx
    vex
    va
    vy
    weq
    vb
    vx
    weq
    wa
    #
    @33
    @27
    vc
    @5
    @35
    @32
    @26
    @0
    @30
    @31
    @2
    @1
    preq12
    eqeq2d
    rexbidv
    @6
    @34
    vx
    vy
    va
    vb
    vx
    va
    weq
    vy
    vb
    weq
    wa
    #
    @4
    @33
    vc
    @5
    @36
    @3
    @32
    @0
    @1
    @2
    @30
    @31
    preq12
    eqeq2d
    rexbidv
    cbvopabv
    braba
    3bitr4g
    ralrimivva
    jca
    @8
    @5
    @17
    cpw
    #
    wcel
    @18
    cP
    @37
    @5
    sprsymrelf.p
    eleq2i
    @5
    @17
    vp
    vex
    elpw
    bitri
    @14
    @24
    vr
    @7
    @15
    @9
    @7
    wceq
    #
    @13
    @23
    vx
    cV
    vx
    @9
    @7
    @6
    vx
    vy
    nfopab1
    nfeq2
    @38
    @12
    @22
    vy
    cV
    vy
    @9
    @7
    @6
    vx
    vy
    nfopab2
    nfeq2
    @38
    @10
    @20
    @11
    @21
    @1
    @2
    @9
    @7
    breq
    @2
    @1
    @9
    @7
    breq
    bibi12d
    ralbid
    ralbid
    elrab
    3imtr4i
    sprsymrelf.r
    syl6eleqr
    fmpti
end
