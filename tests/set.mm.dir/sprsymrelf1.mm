include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "sprsymrelf.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wrex.mm"
include "copab.mm"
include "sprsymrelfv.mm"
include "eqeqan12d.mm"
include "cspr.mm"
include "wss.mm"
include "cpw.mm"
include "eleq2i.mm"
include "vex.mm"
include "elpw.mm"
include "bitri.mm"
include "sprsymrelf1lem.mm"
include "imp.mm"
include "eqcom.mm"
include "syl5bi.mm"
include "ancoms.mm"
include "eqssd.mm"
include "ex.mm"
include "syl2anb.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem sprsymrelf1
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
  disjoint F a
  disjoint F b
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint k x
  assert |- F : P -1-1-> R

  proof
    cP
    cR
    cF
    wf1
    cP
    cR
    cF
    wf
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    cP
    wral
    va
    cP
    wral
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
    @6
    va
    vb
    cP
    @0
    cP
    wcel
    #
    @2
    cP
    wcel
    #
    wa
    @4
    vc
    cv
    vx
    cv
    vy
    cv
    cpr
    wceq
    #
    vc
    @0
    wrex
    vx
    vy
    copab
    #
    @9
    vc
    @2
    wrex
    vx
    vy
    copab
    #
    wceq
    #
    @5
    @7
    @8
    @1
    @10
    @3
    @11
    vx
    vy
    cP
    cR
    cF
    cV
    @0
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    sprsymrelf.f
    sprsymrelfv
    vx
    vy
    cP
    cR
    cF
    cV
    @2
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    sprsymrelf.f
    sprsymrelfv
    eqeqan12d
    @7
    @0
    cV
    cspr
    cfv
    #
    wss
    #
    @2
    @13
    wss
    #
    @12
    @5
    wi
    @8
    @7
    @0
    @13
    cpw
    #
    wcel
    @14
    cP
    @16
    @0
    sprsymrelf.p
    eleq2i
    @0
    @13
    va
    vex
    elpw
    bitri
    @8
    @2
    @16
    wcel
    @15
    cP
    @16
    @2
    sprsymrelf.p
    eleq2i
    @2
    @13
    vb
    vex
    elpw
    bitri
    @14
    @15
    wa
    #
    @12
    @5
    @17
    @12
    wa
    @0
    @2
    @17
    @12
    @0
    @2
    wss
    vx
    vy
    cV
    va
    vb
    vc
    sprsymrelf1lem
    imp
    @17
    @12
    @2
    @0
    wss
    #
    @15
    @14
    @12
    @18
    wi
    @12
    @11
    @10
    wceq
    @15
    @14
    wa
    @18
    @10
    @11
    eqcom
    vx
    vy
    cV
    vb
    va
    vc
    sprsymrelf1lem
    syl5bi
    ancoms
    imp
    eqssd
    ex
    syl2anb
    sylbid
    rgen2a
    va
    vb
    cP
    cR
    cF
    dff13
    mpbir2an
end
