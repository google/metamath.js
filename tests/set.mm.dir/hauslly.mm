include "cha.mm"
include "clly.mm"
include "wss.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "resthaus.mm"
include "adantl.mm"
include "ctop.mm"
include "haustop.mm"
include "ssriv.mm"
include "a1i.mm"
include "restlly.mm"
include "trud.mm"
include "sseli.mm"

theorem hauslly
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


  assert |- ( J e. Haus -> J e. Locally Haus )

  proof
    cha
    cha
    clly
    #
    cJ
    cha
    @0
    wss
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
    @1
    wcel
    wa
    @1
    @2
    crest
    co
    cha
    wcel
    wtru
    @2
    @1
    @1
    resthaus
    adantl
    cha
    ctop
    wss
    wtru
    vj
    cha
    ctop
    @1
    haustop
    ssriv
    a1i
    restlly
    trud
    sseli
end
