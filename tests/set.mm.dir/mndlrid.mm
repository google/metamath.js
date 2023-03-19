include "cmnd.mm"
include "wcel.mm"
include "mndid.mm"
include "mgmlrid.mm"

theorem mndlrid
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume mndlrid.b: |- B = ( Base ` G )
  assume mndlrid.p: |- .+ = ( +g ` G )
  assume mndlrid.o: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Mnd /\ X e. B ) -> ( ( .0. .+ X ) = X /\ ( X .+ .0. ) = X ) )

  proof
    cG
    cmnd
    wcel
    vx
    cB
    c.pl
    vy
    cG
    cX
    c.0
    mndlrid.b
    mndlrid.o
    mndlrid.p
    vx
    vy
    cB
    c.pl
    cG
    mndlrid.b
    mndlrid.p
    mndid
    mgmlrid
end
