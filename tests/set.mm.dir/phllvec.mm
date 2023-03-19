include "cphl.mm"
include "wcel.mm"
include "clvec.mm"
include "csca.mm"
include "cfv.mm"
include "csr.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "cmpt.mm"
include "crglmod.mm"
include "clmhm.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "cstv.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "isphl.mm"
include "simp1bi.mm"

theorem phllvec
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let c.xi: class .,
  let c.as: class .*
  let cF: class F
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  let cV: class V
  let cZ: class Z


  assert |- ( W e. PreHil -> W e. LVec )

  proof
    cW
    cphl
    wcel
    cW
    clvec
    wcel
    cW
    csca
    cfv
    #
    csr
    wcel
    vy
    cW
    cbs
    cfv
    #
    vy
    cv
    #
    vx
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cmpt
    cW
    @0
    crglmod
    cfv
    clmhm
    co
    wcel
    @3
    @3
    @4
    co
    @0
    c0g
    cfv
    #
    wceq
    @3
    cW
    c0g
    cfv
    #
    wceq
    wi
    @3
    @2
    @4
    co
    @0
    cstv
    cfv
    #
    cfv
    @5
    wceq
    vy
    @1
    wral
    w3a
    vx
    @1
    wral
    vx
    vy
    @0
    @4
    @8
    @1
    cW
    @7
    @6
    @1
    eqid
    @0
    eqid
    @4
    eqid
    @7
    eqid
    @8
    eqid
    @6
    eqid
    isphl
    simp1bi
end
