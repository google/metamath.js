include "co.mm"
include "oveq1d.mm"
include "cmnd.mm"
include "wcel.mm"
include "wceq.mm"
include "mndass.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"

theorem mnd12g
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
  assume mnd12g.5: |- ( ph -> ( X .+ Y ) = ( Y .+ X ) )


  assert |- ( ph -> ( X .+ ( Y .+ Z ) ) = ( Y .+ ( X .+ Z ) ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cZ
    c.pl
    co
    #
    cY
    cX
    c.pl
    co
    #
    cZ
    c.pl
    co
    #
    cX
    cY
    cZ
    c.pl
    co
    c.pl
    co
    #
    cY
    cX
    cZ
    c.pl
    co
    c.pl
    co
    #
    wph
    @0
    @2
    cZ
    c.pl
    mnd12g.5
    oveq1d
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
    @1
    @4
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
    @8
    @7
    @9
    @3
    @5
    wceq
    mnd4g.1
    mnd4g.3
    mnd4g.2
    mnd4g.4
    cB
    c.pl
    cG
    cY
    cX
    cZ
    mndcl.b
    mndcl.p
    mndass
    syl13anc
    3eqtr3d
end
