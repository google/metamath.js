include "cdlat.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "clat.mm"
include "isdlat.mm"
include "simprbi.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem dlatmjdi
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vk: setvar k
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isdlat.b: |- B = ( Base ` K )
  assume isdlat.j: |- .\/ = ( join ` K )
  assume isdlat.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. DLat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X ./\ ( Y .\/ Z ) ) = ( ( X ./\ Y ) .\/ ( X ./\ Z ) ) )

  proof
    cK
    cdlat
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
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cY
    cZ
    c.or
    co
    #
    c.an
    co
    #
    cX
    cY
    c.an
    co
    #
    cX
    cZ
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    @0
    cK
    clat
    wcel
    @10
    vx
    vy
    vz
    cB
    c.or
    cK
    c.an
    isdlat.b
    isdlat.j
    isdlat.m
    isdlat
    simprbi
    @9
    @16
    cX
    @4
    c.an
    co
    #
    cX
    @2
    c.an
    co
    #
    cX
    @3
    c.an
    co
    #
    c.or
    co
    #
    wceq
    cX
    cY
    @3
    c.or
    co
    #
    c.an
    co
    #
    @13
    @19
    c.or
    co
    #
    wceq
    vx
    vy
    vz
    cX
    cY
    cZ
    cB
    cB
    cB
    @1
    cX
    wceq
    #
    @5
    @17
    @8
    @20
    @1
    cX
    @4
    c.an
    oveq1
    @24
    @6
    @18
    @7
    @19
    c.or
    @1
    cX
    @2
    c.an
    oveq1
    @1
    cX
    @3
    c.an
    oveq1
    oveq12d
    eqeq12d
    @2
    cY
    wceq
    #
    @17
    @22
    @20
    @23
    @25
    @4
    @21
    cX
    c.an
    @2
    cY
    @3
    c.or
    oveq1
    oveq2d
    @25
    @18
    @13
    @19
    c.or
    @2
    cY
    cX
    c.an
    oveq2
    oveq1d
    eqeq12d
    @3
    cZ
    wceq
    #
    @22
    @12
    @23
    @15
    @26
    @21
    @11
    cX
    c.an
    @3
    cZ
    cY
    c.or
    oveq2
    oveq2d
    @26
    @19
    @14
    @13
    c.or
    @3
    cZ
    cX
    c.an
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    mpan9
end
