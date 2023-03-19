include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cpl1.mm"
include "mplbaspropd.mm"
include "cps1.mm"
include "eqid.mm"
include "ply1bas.mm"
include "3eqtr4g.mm"

theorem ply1baspropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  assume ply1baspropd.b1: |- ( ph -> B = ( Base ` R ) )
  assume ply1baspropd.b2: |- ( ph -> B = ( Base ` S ) )
  assume ply1baspropd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` R ) y ) = ( x ( +g ` S ) y ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( Base ` ( Poly1 ` R ) ) = ( Base ` ( Poly1 ` S ) ) )

  proof
    wph
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    c1o
    cS
    cmpl
    co
    cbs
    cfv
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    cS
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wph
    vx
    vy
    cB
    cR
    cS
    c1o
    ply1baspropd.b1
    ply1baspropd.b2
    ply1baspropd.p
    mplbaspropd
    @0
    cR
    cR
    cps1
    cfv
    #
    @1
    @0
    eqid
    @4
    eqid
    @1
    eqid
    ply1bas
    @2
    cS
    cS
    cps1
    cfv
    #
    @3
    @2
    eqid
    @5
    eqid
    @3
    eqid
    ply1bas
    3eqtr4g
end
