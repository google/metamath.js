include "c0.mm"
include "cxr.mm"
include "wss.mm"
include "cmnf.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "csup.mm"
include "wceq.mm"
include "0ss.mm"
include "mnfxr.mm"
include "ral0.mm"
include "rexr.mm"
include "nltmnf.mm"
include "syl.mm"
include "pm2.21d.mm"
include "rgen.mm"
include "supxr.mm"
include "mp4an.mm"

theorem xrsup0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B


  assert |- sup ( (/) , RR* , < ) = -oo

  proof
    c0
    cxr
    wss
    cmnf
    cxr
    wcel
    cmnf
    vy
    cv
    #
    clt
    wbr
    wn
    #
    vy
    c0
    wral
    @0
    cmnf
    clt
    wbr
    #
    @0
    vz
    cv
    clt
    wbr
    vz
    c0
    wrex
    #
    wi
    #
    vy
    cr
    wral
    c0
    cxr
    clt
    csup
    cmnf
    wceq
    cxr
    0ss
    mnfxr
    @1
    vy
    ral0
    @4
    vy
    cr
    @0
    cr
    wcel
    #
    @2
    @3
    @5
    @0
    cxr
    wcel
    @2
    wn
    @0
    rexr
    @0
    nltmnf
    syl
    pm2.21d
    rgen
    vy
    vz
    c0
    cmnf
    supxr
    mp4an
end
