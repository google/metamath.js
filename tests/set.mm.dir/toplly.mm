include "ctop.mm"
include "clly.mm"
include "cv.mm"
include "llytop.mm"
include "ssriv.mm"
include "wss.mm"
include "wtru.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "resttop.mm"
include "adantl.mm"
include "ssid.mm"
include "a1i.mm"
include "restlly.mm"
include "trud.mm"
include "eqssi.mm"

theorem toplly
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cA: class A
  let cV: class V
  let cX: class X
  let cJ: class J


  assert |- Locally Top = Top

  proof
    ctop
    clly
    #
    ctop
    vj
    @0
    ctop
    ctop
    vj
    cv
    #
    llytop
    ssriv
    ctop
    @0
    wss
    wtru
    vx
    ctop
    vj
    @1
    ctop
    wcel
    vx
    cv
    #
    @1
    wcel
    wa
    @1
    @2
    crest
    co
    ctop
    wcel
    wtru
    @2
    @1
    @1
    resttop
    adantl
    ctop
    ctop
    wss
    wtru
    ctop
    ssid
    a1i
    restlly
    trud
    eqssi
end
