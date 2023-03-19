include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cpw.mm"
include "cdif.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "cldval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "wb.mm"
include "topopn.mm"
include "elpw2g.mm"
include "syl.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem iscld
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( J e. Top -> ( S e. ( Clsd ` J ) <-> ( S C_ X /\ ( X \ S ) e. J ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    cX
    cpw
    #
    wcel
    #
    cX
    cS
    cdif
    #
    cJ
    wcel
    #
    wa
    #
    cS
    cX
    wss
    #
    @6
    wa
    @0
    @2
    cS
    cX
    vx
    cv
    #
    cdif
    #
    cJ
    wcel
    #
    vx
    @3
    crab
    #
    wcel
    @7
    @0
    @1
    @12
    cS
    vx
    cJ
    cX
    iscld.1
    cldval
    eleq2d
    @11
    @6
    vx
    cS
    @3
    @9
    cS
    wceq
    @10
    @5
    cJ
    @9
    cS
    cX
    difeq2
    eleq1d
    elrab
    syl6bb
    @0
    @4
    @8
    @6
    @0
    cX
    cJ
    wcel
    @4
    @8
    wb
    cJ
    cX
    iscld.1
    topopn
    cS
    cX
    cJ
    elpw2g
    syl
    anbi1d
    bitrd
end
