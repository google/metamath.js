include "cr.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "c1.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cc.mm"
include "reflcl.mm"
include "resubcl.mm"
include "mpdan.mm"
include "recnd.mm"
include "adantl.mm"
include "1red.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "id.mm"
include "flle.mm"
include "abssubge0d.mm"
include "fracle1.mm"
include "eqbrtrd.mm"
include "ad2antrl.mm"
include "elo1d.mm"
include "trud.mm"

theorem flo1
  let vx: setvar x
  let vn: setvar n
  let vy: setvar y
  let cA: class A


  assert |- ( x e. RR |-> ( x - ( |_ ` x ) ) ) e. O(1)

  proof
    vx
    cr
    vx
    cv
    #
    @0
    cfl
    cfv
    #
    cmin
    co
    #
    cmpt
    co1
    wcel
    wtru
    vx
    cr
    @2
    c1
    c1
    cr
    cr
    wss
    wtru
    cr
    ssid
    a1i
    @0
    cr
    wcel
    #
    @2
    cc
    wcel
    wtru
    @3
    @2
    @3
    @1
    cr
    wcel
    @2
    cr
    wcel
    @0
    reflcl
    #
    @0
    @1
    resubcl
    mpdan
    recnd
    adantl
    wtru
    1red
    #
    @5
    @3
    @2
    cabs
    cfv
    #
    c1
    cle
    wbr
    wtru
    c1
    @0
    cle
    wbr
    @3
    @6
    @2
    c1
    cle
    @3
    @1
    @0
    @4
    @3
    id
    @0
    flle
    abssubge0d
    @0
    fracle1
    eqbrtrd
    ad2antrl
    elo1d
    trud
end
