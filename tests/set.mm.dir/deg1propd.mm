include "c1o.mm"
include "cmdg.mm"
include "co.mm"
include "cdg1.mm"
include "cfv.mm"
include "mdegpropd.mm"
include "eqid.mm"
include "deg1fval.mm"
include "3eqtr4g.mm"

theorem deg1propd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  assume deg1propd.b1: |- ( ph -> B = ( Base ` R ) )
  assume deg1propd.b2: |- ( ph -> B = ( Base ` S ) )
  assume deg1propd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` R ) y ) = ( x ( +g ` S ) y ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( deg1 ` R ) = ( deg1 ` S ) )

  proof
    wph
    c1o
    cR
    cmdg
    co
    c1o
    cS
    cmdg
    co
    cR
    cdg1
    cfv
    #
    cS
    cdg1
    cfv
    #
    wph
    vx
    vy
    cB
    cR
    cS
    c1o
    deg1propd.b1
    deg1propd.b2
    deg1propd.p
    mdegpropd
    @0
    cR
    @0
    eqid
    deg1fval
    @1
    cS
    @1
    eqid
    deg1fval
    3eqtr4g
end
