include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "codd.mm"
include "cgbow.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "df-gbow.mm"
include "elrab2.mm"

theorem isgbow
  let cZ: class Z
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x

  disjoint Z p
  disjoint Z q
  disjoint Z r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint Z z
  disjoint p z
  disjoint q z
  disjoint r z
  disjoint k x
  assert |- ( Z e. GoldbachOddW <-> ( Z e. Odd /\ E. p e. Prime E. q e. Prime E. r e. Prime Z = ( ( p + q ) + r ) ) )

  proof
    vz
    cv
    #
    vp
    cv
    vq
    cv
    caddc
    co
    vr
    cv
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    cZ
    @1
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    vz
    cZ
    codd
    cgbow
    @0
    cZ
    wceq
    #
    @3
    @5
    vp
    vq
    cprime
    cprime
    @6
    @2
    @4
    vr
    cprime
    @0
    cZ
    @1
    eqeq1
    rexbidv
    2rexbidv
    vz
    vr
    vq
    vp
    df-gbow
    elrab2
end
