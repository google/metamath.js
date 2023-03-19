include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "riotabidv.mm"
include "grpinvfval.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem grpinvval
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vx: setvar x
  assume grpinvval.b: |- B = ( Base ` G )
  assume grpinvval.p: |- .+ = ( +g ` G )
  assume grpinvval.o: |- .0. = ( 0g ` G )
  assume grpinvval.n: |- N = ( invg ` G )

  disjoint B y
  disjoint G y
  disjoint X y
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint x y
  disjoint B x
  disjoint G g
  disjoint G x
  disjoint .0. g
  disjoint .0. x
  disjoint .+ g
  disjoint .+ x
  disjoint X x
  assert |- ( X e. B -> ( N ` X ) = ( iota_ y e. B ( y .+ X ) = .0. ) )

  proof
    vx
    cX
    vy
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    crio
    @0
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    crio
    cB
    cN
    @1
    cX
    wceq
    #
    @3
    @5
    vy
    cB
    @6
    @2
    @4
    c.0
    @1
    cX
    @0
    c.pl
    oveq2
    eqeq1d
    riotabidv
    vx
    vy
    cB
    c.pl
    cG
    cN
    c.0
    grpinvval.b
    grpinvval.p
    grpinvval.o
    grpinvval.n
    grpinvfval
    @5
    vy
    cB
    riotaex
    fvmpt
end
