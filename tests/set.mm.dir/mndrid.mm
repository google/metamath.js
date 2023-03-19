include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "mndlrid.mm"
include "simprd.mm"

theorem mndrid
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


  assert |- ( ( G e. Mnd /\ X e. B ) -> ( X .+ .0. ) = X )

  proof
    cG
    cmnd
    wcel
    cX
    cB
    wcel
    wa
    c.0
    cX
    c.pl
    co
    cX
    wceq
    cX
    c.0
    c.pl
    co
    cX
    wceq
    cB
    c.pl
    cG
    cX
    c.0
    mndlrid.b
    mndlrid.p
    mndlrid.o
    mndlrid
    simprd
end
