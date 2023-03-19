include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "clss.mm"
include "cfv.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "wn.mm"
include "wceq.mm"
include "cbs.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "sseq2d.mm"
include "biimpcd.mm"
include "ss0.mm"
include "syl6.mm"
include "necon1ad.mm"
include "imp.mm"
include "3adant3.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "lssset.mm"
include "eleq2d.mm"
include "wa.mm"
include "eldifsn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "ralbidv.mm"
include "elrab.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem islss
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vw: setvar w
  assume lssset.f: |- F = ( Scalar ` W )
  assume lssset.b: |- B = ( Base ` F )
  assume lssset.v: |- V = ( Base ` W )
  assume lssset.p: |- .+ = ( +g ` W )
  assume lssset.t: |- .x. = ( .s ` W )
  assume lssset.s: |- S = ( LSubSp ` W )

  disjoint B x
  disjoint a b
  disjoint a x
  disjoint W a
  disjoint b x
  disjoint W b
  disjoint W x
  disjoint U a
  disjoint U b
  disjoint U x
  disjoint s w
  disjoint .+ s
  disjoint .+ w
  disjoint s x
  disjoint B s
  disjoint w x
  disjoint B w
  disjoint V s
  disjoint V w
  disjoint a s
  disjoint a w
  disjoint b s
  disjoint b w
  disjoint W s
  disjoint W w
  disjoint .x. s
  disjoint .x. w
  disjoint U s
  assert |- ( U e. S <-> ( U C_ V /\ U =/= (/) /\ A. x e. B A. a e. U A. b e. U ( ( x .x. a ) .+ b ) e. U ) )

  proof
    cU
    cS
    wcel
    #
    cW
    cvv
    wcel
    #
    cU
    cV
    wss
    #
    cU
    c0
    wne
    #
    vx
    cv
    va
    cv
    c.x
    co
    vb
    cv
    c.pl
    co
    #
    cU
    wcel
    #
    vb
    cU
    wral
    #
    va
    cU
    wral
    #
    vx
    cB
    wral
    #
    w3a
    #
    @1
    cU
    cW
    clss
    cfv
    cS
    cU
    cW
    clss
    elfvex
    lssset.s
    eleq2s
    @2
    @3
    @1
    @8
    @2
    @3
    @1
    @2
    @1
    cU
    c0
    @2
    @1
    wn
    #
    cU
    c0
    wss
    #
    cU
    c0
    wceq
    @10
    @2
    @11
    @10
    cV
    c0
    cU
    @10
    cV
    cW
    cbs
    cfv
    #
    c0
    lssset.v
    cW
    cbs
    fvprc
    syl5eq
    sseq2d
    biimpcd
    cU
    ss0
    syl6
    necon1ad
    imp
    3adant3
    @1
    @0
    cU
    @4
    vs
    cv
    #
    wcel
    #
    vb
    @13
    wral
    #
    va
    @13
    wral
    #
    vx
    cB
    wral
    #
    vs
    cV
    cpw
    #
    c0
    csn
    cdif
    #
    crab
    #
    wcel
    #
    @9
    @1
    cS
    @20
    cU
    vx
    cB
    c.pl
    cS
    c.x
    cF
    cV
    cW
    cvv
    vs
    va
    vb
    lssset.f
    lssset.b
    lssset.v
    lssset.p
    lssset.t
    lssset.s
    lssset
    eleq2d
    cU
    @19
    wcel
    #
    @8
    wa
    @2
    @3
    wa
    #
    @8
    wa
    @21
    @9
    @22
    @23
    @8
    @22
    cU
    @18
    wcel
    #
    @3
    wa
    @23
    cU
    @18
    c0
    eldifsn
    @24
    @2
    @3
    cU
    cV
    cV
    @12
    cvv
    lssset.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    anbi1i
    bitri
    anbi1i
    @17
    @8
    vs
    cU
    @19
    @13
    cU
    wceq
    @16
    @7
    vx
    cB
    @15
    @6
    va
    @13
    cU
    @14
    @5
    vb
    @13
    cU
    @13
    cU
    @4
    eleq2
    raleqbi1dv
    raleqbi1dv
    ralbidv
    elrab
    @2
    @3
    @8
    df-3an
    3bitr4i
    syl6bb
    pm5.21nii
end
