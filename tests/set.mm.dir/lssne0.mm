include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "csn.mm"
include "wceq.mm"
include "wral.mm"
include "wn.mm"
include "c0.mm"
include "wb.mm"
include "lssn0.mm"
include "eqsn.mm"
include "syl.mm"
include "nne.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr3i.mm"
include "syl6rbb.mm"
include "necon1abid.mm"

theorem lssne0
  let vy: setvar y
  let cS: class S
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let cU: class U
  let va: setvar a
  let vb: setvar b
  assume lss0cl.z: |- .0. = ( 0g ` W )
  assume lss0cl.s: |- S = ( LSubSp ` W )

  disjoint X y
  disjoint .0. y
  disjoint S x
  disjoint U x
  disjoint a b
  disjoint a x
  disjoint W a
  disjoint b x
  disjoint W b
  disjoint W x
  disjoint a y
  disjoint .0. a
  disjoint b y
  disjoint .0. b
  disjoint x y
  disjoint .0. x
  assert |- ( X e. S -> ( X =/= { .0. } <-> E. y e. X y =/= .0. ) )

  proof
    cX
    cS
    wcel
    #
    vy
    cv
    #
    c.0
    wne
    #
    vy
    cX
    wrex
    #
    cX
    c.0
    csn
    #
    @0
    cX
    @4
    wceq
    #
    @1
    c.0
    wceq
    #
    vy
    cX
    wral
    #
    @3
    wn
    #
    @0
    cX
    c0
    wne
    @5
    @7
    wb
    cS
    cX
    cW
    lss0cl.s
    lssn0
    vy
    cX
    c.0
    eqsn
    syl
    @7
    @2
    wn
    #
    vy
    cX
    wral
    @8
    @9
    @6
    vy
    cX
    @1
    c.0
    nne
    ralbii
    @2
    vy
    cX
    ralnex
    bitr3i
    syl6rbb
    necon1abid
end
