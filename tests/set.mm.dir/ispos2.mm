include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "w3a.mm"
include "wral.mm"
include "cpo.mm"
include "cpreset.mm"
include "3anan32.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"
include "2ralbii.mm"
include "r19.26-2.mm"
include "rr19.3v.mm"
include "anbi2i.mm"
include "ispos.mm"
include "isprs.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitr4i.mm"

theorem ispos2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vz: setvar z
  assume ispos2.b: |- B = ( Base ` K )
  assume ispos2.l: |- .<_ = ( le ` K )

  disjoint K x
  disjoint K y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint .<_ x
  disjoint .<_ y
  disjoint K z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint .<_ z
  assert |- ( K e. Poset <-> ( K e. Preset /\ A. x e. B A. y e. B ( ( x .<_ y /\ y .<_ x ) -> x = y ) ) )

  proof
    cK
    cvv
    wcel
    #
    vx
    cv
    #
    @1
    c.le
    wbr
    #
    @1
    vy
    cv
    #
    c.le
    wbr
    #
    @3
    @1
    c.le
    wbr
    wa
    vx
    vy
    weq
    wi
    #
    @4
    @3
    vz
    cv
    #
    c.le
    wbr
    wa
    @1
    @6
    c.le
    wbr
    wi
    #
    w3a
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    @0
    @2
    @7
    wa
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @5
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    wa
    #
    cK
    cpo
    wcel
    cK
    cpreset
    wcel
    #
    @15
    wa
    #
    @10
    @16
    @0
    @10
    @12
    @5
    vz
    cB
    wral
    #
    wa
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @16
    @9
    @21
    vx
    vy
    cB
    cB
    @9
    @11
    @5
    wa
    #
    vz
    cB
    wral
    @21
    @8
    @23
    vz
    cB
    @2
    @5
    @7
    3anan32
    ralbii
    @11
    @5
    vz
    cB
    r19.26
    bitri
    2ralbii
    @22
    @13
    @20
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    @16
    @12
    @20
    vx
    vy
    cB
    cB
    r19.26-2
    @25
    @15
    @13
    @24
    @14
    vx
    cB
    @5
    vy
    vz
    cB
    rr19.3v
    ralbii
    anbi2i
    bitri
    bitri
    anbi2i
    vx
    vy
    vz
    cB
    cK
    c.le
    ispos2.b
    ispos2.l
    ispos
    @19
    @0
    @13
    wa
    #
    @15
    wa
    @17
    @18
    @26
    @15
    vx
    vy
    vz
    cB
    cK
    c.le
    ispos2.b
    ispos2.l
    isprs
    anbi1i
    @0
    @13
    @15
    anass
    bitri
    3bitr4i
end
