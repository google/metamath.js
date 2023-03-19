include "cpr.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wcel.mm"
include "wne.mm"
include "wss.mm"
include "prssi.mm"
include "mp2an.mm"
include "prex.mm"
include "elpw.mm"
include "mpbir.mm"
include "elexi.mm"
include "prnz.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "cfn.mm"
include "hashprlei.mm"
include "simpri.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"

theorem upgrbi
  let vx: setvar x
  let cV: class V
  let cX: class X
  let cY: class Y
  assume upgrbi.x: |- X e. V
  assume upgrbi.y: |- Y e. V

  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- { X , Y } e. { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 }

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
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    c0
    csn
    cdif
    #
    crab
    wcel
    @0
    @5
    wcel
    #
    @0
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    @6
    @0
    @4
    wcel
    #
    @0
    c0
    wne
    @9
    @0
    cV
    wss
    #
    cX
    cV
    wcel
    cY
    cV
    wcel
    @10
    upgrbi.x
    upgrbi.y
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
    cX
    cY
    cX
    cV
    upgrbi.x
    elexi
    prnz
    @0
    @4
    c0
    eldifsn
    mpbir2an
    @0
    cfn
    wcel
    @8
    cX
    cY
    hashprlei
    simpri
    @3
    @8
    vx
    @0
    @5
    @1
    @0
    wceq
    @2
    @7
    c2
    cle
    @1
    @0
    chash
    fveq2
    breq1d
    elrab
    mpbir2an
end
