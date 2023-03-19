include "wcel.mm"
include "wtru.mm"
include "cv.mm"
include "ccnv.mm"
include "cdif.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "idd.mm"
include "biidd.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "elex.mm"
include "a1tru.mm"
include "clcnvlem.mm"

theorem cnvtrucl0
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cX: class X

  disjoint x y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  assert |- ( X e. V -> `' |^| { x | ( X C_ x /\ T. ) } = |^| { y | ( `' X C_ y /\ T. ) } )

  proof
    cX
    cV
    wcel
    #
    wtru
    wtru
    wtru
    vx
    vy
    cX
    cX
    @0
    vx
    cv
    #
    vy
    cv
    #
    ccnv
    cX
    cX
    ccnv
    ccnv
    cdif
    cun
    wceq
    wa
    wtru
    idd
    @0
    @2
    @1
    ccnv
    wceq
    wa
    wtru
    idd
    @1
    cX
    wceq
    wtru
    biidd
    cX
    cX
    wss
    @0
    cX
    ssid
    a1i
    cX
    cV
    elex
    @0
    a1tru
    clcnvlem
end
