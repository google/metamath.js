include "cha.mm"
include "cnlly.mm"
include "clly.mm"
include "wceq.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "resthaus.mm"
include "adantl.mm"
include "restnlly.mm"
include "trud.mm"
include "eleq2i.mm"

theorem hausnlly
  let cJ: class J
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


  assert |- ( J e. N-Locally Haus <-> J e. Locally Haus )

  proof
    cha
    cnlly
    #
    cha
    clly
    #
    cJ
    @0
    @1
    wceq
    wtru
    vx
    cha
    vj
    vj
    cv
    #
    cha
    wcel
    vx
    cv
    #
    @2
    wcel
    wa
    @2
    @3
    crest
    co
    cha
    wcel
    wtru
    @3
    @2
    @2
    resthaus
    adantl
    restnlly
    trud
    eleq2i
end
