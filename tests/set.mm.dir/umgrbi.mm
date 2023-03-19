include "cpr.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wcel.mm"
include "wss.mm"
include "prssi.mm"
include "mp2an.mm"
include "prex.mm"
include "elpw.mm"
include "mpbir.mm"
include "wa.mm"
include "wne.mm"
include "hashprg.mm"
include "mpbii.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "mpbir2an.mm"

theorem umgrbi
  let vx: setvar x
  let cV: class V
  let cX: class X
  let cY: class Y
  assume umgrbi.x: |- X e. V
  assume umgrbi.y: |- Y e. V
  assume umgrbi.n: |- X =/= Y

  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- { X , Y } e. { x e. ~P V | ( # ` x ) = 2 }

  proof
    cX
    cY
    cpr
    #
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    wcel
    @0
    @4
    wcel
    #
    @0
    chash
    cfv
    #
    c2
    wceq
    #
    @5
    @0
    cV
    wss
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @8
    umgrbi.x
    umgrbi.y
    cX
    cY
    cV
    prssi
    mp2an
    @0
    cV
    cX
    cY
    prex
    elpw
    mpbir
    @9
    @10
    @7
    umgrbi.x
    umgrbi.y
    @9
    @10
    wa
    cX
    cY
    wne
    @7
    umgrbi.n
    cX
    cY
    cV
    cV
    hashprg
    mpbii
    mp2an
    @3
    @7
    vx
    @0
    @4
    @1
    @0
    wceq
    @2
    @6
    c2
    @1
    @0
    chash
    fveq2
    eqeq1d
    elrab
    mpbir2an
end
