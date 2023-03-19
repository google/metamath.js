include "codd.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cprime.mm"
include "wrex.mm"
include "cgbo.mm"
include "cgbow.mm"
include "simpr.mm"
include "reximi.mm"
include "anim2i.mm"
include "isgbo.mm"
include "isgbow.mm"
include "3imtr4i.mm"

theorem gbogbow
  let cZ: class Z
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOdd -> Z e. GoldbachOddW )

  proof
    cZ
    codd
    wcel
    #
    vp
    cv
    #
    codd
    wcel
    vq
    cv
    #
    codd
    wcel
    vr
    cv
    #
    codd
    wcel
    w3a
    #
    cZ
    @1
    @2
    caddc
    co
    @3
    caddc
    co
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @0
    @5
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    cZ
    cgbo
    wcel
    cZ
    cgbow
    wcel
    @9
    @12
    @0
    @8
    @11
    vp
    cprime
    @7
    @10
    vq
    cprime
    @6
    @5
    vr
    cprime
    @4
    @5
    simpr
    reximi
    reximi
    reximi
    anim2i
    cZ
    vr
    vq
    vp
    isgbo
    cZ
    vr
    vq
    vp
    isgbow
    3imtr4i
end
