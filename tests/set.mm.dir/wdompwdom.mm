include "cwdom.mm"
include "wbr.mm"
include "cpw.mm"
include "cdom.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "pwexg.mm"
include "syl.mm"
include "0ss.mm"
include "sspwb.mm"
include "mpbi.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "pweq.mm"
include "breq1d.mm"
include "syl5ibr.mm"
include "wne.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "brwdomn0.mm"
include "vex.mm"
include "fopwdom.mm"
include "mpan.mm"
include "exlimiv.mm"
include "syl6bi.mm"
include "pm2.61ine.mm"

theorem wdompwdom
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  let cZ: class Z


  assert |- ( X ~<_* Y -> ~P X ~<_ ~P Y )

  proof
    cX
    cY
    cwdom
    wbr
    #
    cX
    cpw
    #
    cY
    cpw
    #
    cdom
    wbr
    #
    wi
    cX
    c0
    @0
    @3
    cX
    c0
    wceq
    #
    c0
    cpw
    #
    @2
    cdom
    wbr
    #
    @0
    @2
    cvv
    wcel
    #
    @5
    @2
    wss
    #
    @6
    @0
    cY
    cvv
    wcel
    @7
    cX
    cY
    cwdom
    relwdom
    brrelex2i
    cY
    cvv
    pwexg
    syl
    c0
    cY
    wss
    @8
    cY
    0ss
    c0
    cY
    sspwb
    mpbi
    @5
    @2
    cvv
    ssdomg
    mpisyl
    @4
    @1
    @5
    @2
    cdom
    cX
    c0
    pweq
    breq1d
    syl5ibr
    cX
    c0
    wne
    @0
    cY
    cX
    vz
    cv
    #
    wfo
    #
    vz
    wex
    @3
    vz
    cX
    cY
    brwdomn0
    @10
    @3
    vz
    @9
    cvv
    wcel
    @10
    @3
    vz
    vex
    cY
    cX
    @9
    cvv
    fopwdom
    mpan
    exlimiv
    syl6bi
    pm2.61ine
end
