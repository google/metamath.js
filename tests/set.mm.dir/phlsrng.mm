include "cphl.mm"
include "wcel.mm"
include "clvec.mm"
include "csr.mm"
include "cbs.mm"
include "cfv.mm"
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
include "simp2bi.mm"

theorem phlsrng
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let c.xi: class .,
  let c.as: class .*
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  let cV: class V
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )


  assert |- ( W e. PreHil -> F e. *Ring )

  proof
    cW
    cphl
    wcel
    cW
    clvec
    wcel
    cF
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
    cF
    crglmod
    cfv
    clmhm
    co
    wcel
    @2
    @2
    @3
    co
    cF
    c0g
    cfv
    #
    wceq
    @2
    cW
    c0g
    cfv
    #
    wceq
    wi
    @2
    @1
    @3
    co
    cF
    cstv
    cfv
    #
    cfv
    @4
    wceq
    vy
    @0
    wral
    w3a
    vx
    @0
    wral
    vx
    vy
    cF
    @3
    @7
    @0
    cW
    @6
    @5
    @0
    eqid
    phlsrng.f
    @3
    eqid
    @6
    eqid
    @7
    eqid
    @5
    eqid
    isphl
    simp2bi
end
