include "cbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "isbnd.mm"
include "simplbi.mm"

theorem bndmet
  let cM: class M
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cP: class P
  let cR: class R
  let cS: class S
  let cY: class Y


  assert |- ( M e. ( Bnd ` X ) -> M e. ( Met ` X ) )

  proof
    cM
    cX
    cbnd
    cfv
    wcel
    cM
    cX
    cme
    cfv
    wcel
    cX
    vx
    cv
    vy
    cv
    cM
    cbl
    cfv
    co
    wceq
    vy
    crp
    wrex
    vx
    cX
    wral
    vx
    cM
    cX
    vy
    isbnd
    simplbi
end
