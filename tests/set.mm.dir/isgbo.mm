include "cv.mm"
include "codd.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cprime.mm"
include "wrex.mm"
include "cgbo.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "df-gbo.mm"
include "elrab2.mm"

theorem isgbo
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
  assert |- ( Z e. GoldbachOdd <-> ( Z e. Odd /\ E. p e. Prime E. q e. Prime E. r e. Prime ( ( p e. Odd /\ q e. Odd /\ r e. Odd ) /\ Z = ( ( p + q ) + r ) ) ) )

  proof
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
    vz
    cv
    #
    @0
    @1
    caddc
    co
    @2
    caddc
    co
    #
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
    vp
    cprime
    wrex
    @3
    cZ
    @5
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
    vp
    cprime
    wrex
    vz
    cZ
    codd
    cgbo
    @4
    cZ
    wceq
    #
    @8
    @11
    vp
    vq
    cprime
    cprime
    @12
    @7
    @10
    vr
    cprime
    @12
    @6
    @9
    @3
    @4
    cZ
    @5
    eqeq1
    anbi2d
    rexbidv
    2rexbidv
    vz
    vr
    vq
    vp
    df-gbo
    elrab2
end
