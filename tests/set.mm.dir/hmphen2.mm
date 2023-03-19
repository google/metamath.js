include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cen.mm"
include "hmph.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "wf1o.mm"
include "hmeof1o.mm"
include "f1oen3g.mm"
include "mpdan.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem hmphen2
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cF: class F
  let vx: setvar x
  let vf: setvar f
  assume cmphaushmeo.1: |- X = U. J
  assume cmphaushmeo.2: |- Y = U. K


  assert |- ( J ~= K -> X ~~ Y )

  proof
    cJ
    cK
    chmph
    wbr
    cJ
    cK
    chmeo
    co
    #
    c0
    wne
    #
    cX
    cY
    cen
    wbr
    #
    cJ
    cK
    hmph
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    n0
    @4
    @2
    vf
    @4
    cX
    cY
    @3
    wf1o
    @2
    @3
    cJ
    cK
    cX
    cY
    cmphaushmeo.1
    cmphaushmeo.2
    hmeof1o
    cX
    cY
    @3
    @0
    f1oen3g
    mpdan
    exlimiv
    sylbi
    sylbi
end
