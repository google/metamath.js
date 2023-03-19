include "cv.mm"
include "codd.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "ceven.mm"
include "cgbe.mm"
include "eqeq1.mm"
include "3anbi3d.mm"
include "2rexbidv.mm"
include "df-gbe.mm"
include "elrab2.mm"

theorem isgbe
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let vz: setvar z
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x

  disjoint Z p
  disjoint Z q
  disjoint p q
  disjoint Z z
  disjoint Z r
  disjoint p z
  disjoint q z
  disjoint r z
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- ( Z e. GoldbachEven <-> ( Z e. Even /\ E. p e. Prime E. q e. Prime ( p e. Odd /\ q e. Odd /\ Z = ( p + q ) ) ) )

  proof
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    vz
    cv
    #
    @0
    @2
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    @1
    @3
    cZ
    @5
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    vz
    cZ
    ceven
    cgbe
    @4
    cZ
    wceq
    #
    @7
    @9
    vp
    vq
    cprime
    cprime
    @10
    @6
    @8
    @1
    @3
    @4
    cZ
    @5
    eqeq1
    3anbi3d
    2rexbidv
    vz
    vq
    vp
    df-gbe
    elrab2
end
