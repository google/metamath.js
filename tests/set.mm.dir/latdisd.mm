include "clat.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "latdisdlem.mm"
include "codu.mm"
include "cfv.mm"
include "wi.mm"
include "eqid.mm"
include "odulat.mm"
include "odubas.mm"
include "odujoin.mm"
include "odumeet.mm"
include "syl.mm"
include "impbid.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvral3v.mm"
include "syl6bb.mm"

theorem latdisd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume latdisd.b: |- B = ( Base ` K )
  assume latdisd.j: |- .\/ = ( join ` K )
  assume latdisd.m: |- ./\ = ( meet ` K )

  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ w
  disjoint ./\ u
  disjoint ./\ v
  disjoint ./\ w
  assert |- ( K e. Lat -> ( A. x e. B A. y e. B A. z e. B ( x .\/ ( y ./\ z ) ) = ( ( x .\/ y ) ./\ ( x .\/ z ) ) <-> A. x e. B A. y e. B A. z e. B ( x ./\ ( y .\/ z ) ) = ( ( x ./\ y ) .\/ ( x ./\ z ) ) ) )

  proof
    cK
    clat
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    c.an
    co
    c.or
    co
    @1
    @2
    c.or
    co
    @1
    @3
    c.or
    co
    c.an
    co
    wceq
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vu
    cv
    #
    vv
    cv
    #
    vw
    cv
    #
    c.or
    co
    #
    c.an
    co
    #
    @5
    @6
    c.an
    co
    #
    @5
    @7
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    vw
    cB
    wral
    vv
    cB
    wral
    vu
    cB
    wral
    #
    @1
    @2
    @3
    c.or
    co
    #
    c.an
    co
    #
    @1
    @2
    c.an
    co
    #
    @1
    @3
    c.an
    co
    #
    c.or
    co
    #
    wceq
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
    @0
    @4
    @14
    vu
    vv
    vw
    vz
    vy
    vx
    cB
    c.or
    cK
    c.an
    latdisd.b
    latdisd.j
    latdisd.m
    latdisdlem
    @0
    cK
    codu
    cfv
    #
    clat
    wcel
    @14
    @4
    wi
    @21
    cK
    @21
    eqid
    #
    odulat
    vx
    vy
    vz
    vw
    vv
    vu
    cB
    c.an
    @21
    c.or
    cB
    @21
    cK
    @22
    latdisd.b
    odubas
    @21
    c.an
    cK
    @22
    latdisd.m
    odujoin
    @21
    c.or
    cK
    @22
    latdisd.j
    odumeet
    latdisdlem
    syl
    impbid
    @13
    @20
    @1
    @8
    c.an
    co
    #
    @1
    @6
    c.an
    co
    #
    @1
    @7
    c.an
    co
    #
    c.or
    co
    #
    wceq
    @1
    @2
    @7
    c.or
    co
    #
    c.an
    co
    #
    @17
    @25
    c.or
    co
    #
    wceq
    vu
    vv
    vw
    vx
    vy
    vz
    cB
    cB
    cB
    vu
    vx
    weq
    #
    @9
    @23
    @12
    @26
    @5
    @1
    @8
    c.an
    oveq1
    @30
    @10
    @24
    @11
    @25
    c.or
    @5
    @1
    @6
    c.an
    oveq1
    @5
    @1
    @7
    c.an
    oveq1
    oveq12d
    eqeq12d
    vv
    vy
    weq
    #
    @23
    @28
    @26
    @29
    @31
    @8
    @27
    @1
    c.an
    @6
    @2
    @7
    c.or
    oveq1
    oveq2d
    @31
    @24
    @17
    @25
    c.or
    @6
    @2
    @1
    c.an
    oveq2
    oveq1d
    eqeq12d
    vw
    vz
    weq
    #
    @28
    @16
    @29
    @19
    @32
    @27
    @15
    @1
    c.an
    @7
    @3
    @2
    c.or
    oveq2
    oveq2d
    @32
    @25
    @18
    @17
    c.or
    @7
    @3
    @1
    c.an
    oveq2
    oveq2d
    eqeq12d
    cbvral3v
    syl6bb
end
