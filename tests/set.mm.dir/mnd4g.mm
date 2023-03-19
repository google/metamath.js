include "co.mm"
include "mnd12g.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "wcel.mm"
include "wceq.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "mndass.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"

theorem mnd4g
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cW: class W
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
  assume mnd4g.5: |- ( ph -> W e. B )
  assume mnd4g.6: |- ( ph -> ( Y .+ Z ) = ( Z .+ Y ) )


  assert |- ( ph -> ( ( X .+ Y ) .+ ( Z .+ W ) ) = ( ( X .+ Z ) .+ ( Y .+ W ) ) )

  proof
    wph
    cX
    cY
    cZ
    cW
    c.pl
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cZ
    cY
    cW
    c.pl
    co
    #
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
    @0
    c.pl
    co
    #
    cX
    cZ
    c.pl
    co
    @3
    c.pl
    co
    #
    wph
    @1
    @4
    cX
    c.pl
    wph
    cB
    c.pl
    cG
    cY
    cZ
    cW
    mndcl.b
    mndcl.p
    mnd4g.1
    mnd4g.3
    mnd4g.4
    mnd4g.5
    mnd4g.6
    mnd12g
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
    @0
    cB
    wcel
    #
    @6
    @2
    wceq
    mnd4g.1
    mnd4g.2
    mnd4g.3
    wph
    @8
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @11
    mnd4g.1
    mnd4g.4
    mnd4g.5
    cB
    c.pl
    cG
    cZ
    cW
    mndcl.b
    mndcl.p
    mndcl
    syl3anc
    cB
    c.pl
    cG
    cX
    cY
    @0
    mndcl.b
    mndcl.p
    mndass
    syl13anc
    wph
    @8
    @9
    @12
    @3
    cB
    wcel
    #
    @7
    @5
    wceq
    mnd4g.1
    mnd4g.2
    mnd4g.4
    wph
    @8
    @10
    @13
    @14
    mnd4g.1
    mnd4g.3
    mnd4g.5
    cB
    c.pl
    cG
    cY
    cW
    mndcl.b
    mndcl.p
    mndcl
    syl3anc
    cB
    c.pl
    cG
    cX
    cZ
    @3
    mndcl.b
    mndcl.p
    mndass
    syl13anc
    3eqtr4d
end
