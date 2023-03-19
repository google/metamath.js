include "co.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "wcel.mm"
include "wceq.mm"
include "mndass.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"

theorem mnd32g
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  assume mndcl.b: |- B = ( Base ` G )
  assume mndcl.p: |- .+ = ( +g ` G )
  assume mnd4g.1: |- ( ph -> G e. Mnd )
  assume mnd4g.2: |- ( ph -> X e. B )
  assume mnd4g.3: |- ( ph -> Y e. B )
  assume mnd4g.4: |- ( ph -> Z e. B )
  assume mnd32g.5: |- ( ph -> ( Y .+ Z ) = ( Z .+ Y ) )


  assert |- ( ph -> ( ( X .+ Y ) .+ Z ) = ( ( X .+ Z ) .+ Y ) )

  proof
    wph
    cX
    cY
    cZ
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cZ
    cY
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    #
    cX
    cZ
    c.pl
    co
    cY
    c.pl
    co
    #
    wph
    @0
    @2
    cX
    c.pl
    mnd32g.5
    oveq2d
    wph
    cG
    cmnd
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    @4
    @1
    wceq
    mnd4g.1
    mnd4g.2
    mnd4g.3
    mnd4g.4
    cB
    c.pl
    cG
    cX
    cY
    cZ
    mndcl.b
    mndcl.p
    mndass
    syl13anc
    wph
    @6
    @7
    @9
    @8
    @5
    @3
    wceq
    mnd4g.1
    mnd4g.2
    mnd4g.4
    mnd4g.3
    cB
    c.pl
    cG
    cX
    cZ
    cY
    mndcl.b
    mndcl.p
    mndass
    syl13anc
    3eqtr4d
end
