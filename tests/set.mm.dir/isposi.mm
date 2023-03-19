include "cpo.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "w3a.mm"
include "wral.mm"
include "3ad2ant1.mm"
include "3adant3.mm"
include "3jca.mm"
include "rgen3.mm"
include "ispos.mm"
include "mpbir2an.mm"

theorem isposi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  assume isposi.k: |- K e. _V
  assume isposi.b: |- B = ( Base ` K )
  assume isposi.l: |- .<_ = ( le ` K )
  assume isposi.1: |- ( x e. B -> x .<_ x )
  assume isposi.2: |- ( ( x e. B /\ y e. B ) -> ( ( x .<_ y /\ y .<_ x ) -> x = y ) )
  assume isposi.3: |- ( ( x e. B /\ y e. B /\ z e. B ) -> ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  assert |- K e. Poset

  proof
    cK
    cpo
    wcel
    cK
    cvv
    wcel
    vx
    cv
    #
    @0
    c.le
    wbr
    #
    @0
    vy
    cv
    #
    c.le
    wbr
    #
    @2
    @0
    c.le
    wbr
    wa
    vx
    vy
    weq
    wi
    #
    @3
    @2
    vz
    cv
    #
    c.le
    wbr
    wa
    @0
    @5
    c.le
    wbr
    wi
    #
    w3a
    #
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    isposi.k
    @7
    vx
    vy
    vz
    cB
    cB
    cB
    @0
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    w3a
    @1
    @4
    @6
    @8
    @9
    @1
    @10
    isposi.1
    3ad2ant1
    @8
    @9
    @4
    @10
    isposi.2
    3adant3
    isposi.3
    3jca
    rgen3
    vx
    vy
    vz
    cB
    cK
    c.le
    isposi.b
    isposi.l
    ispos
    mpbir2an
end
