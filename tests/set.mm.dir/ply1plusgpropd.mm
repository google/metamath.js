include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cpl1.mm"
include "cmps.mm"
include "psrplusgpropd.mm"
include "eqid.mm"
include "mplplusg.mm"
include "3eqtr4g.mm"
include "ply1plusg.mm"

theorem ply1plusgpropd
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
  assert |- ( ph -> ( +g ` ( Poly1 ` R ) ) = ( +g ` ( Poly1 ` S ) ) )

  proof
    wph
    c1o
    cR
    cmpl
    co
    #
    cplusg
    cfv
    #
    c1o
    cS
    cmpl
    co
    #
    cplusg
    cfv
    #
    cR
    cpl1
    cfv
    #
    cplusg
    cfv
    #
    cS
    cpl1
    cfv
    #
    cplusg
    cfv
    #
    wph
    c1o
    cR
    cmps
    co
    #
    cplusg
    cfv
    c1o
    cS
    cmps
    co
    #
    cplusg
    cfv
    @1
    @3
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
    psrplusgpropd
    @1
    cR
    @8
    c1o
    @0
    @0
    eqid
    #
    @8
    eqid
    @1
    eqid
    mplplusg
    @3
    cS
    @9
    c1o
    @2
    @2
    eqid
    #
    @9
    eqid
    @3
    eqid
    mplplusg
    3eqtr4g
    @5
    cR
    @0
    @4
    @4
    eqid
    @10
    @5
    eqid
    ply1plusg
    @7
    cS
    @2
    @6
    @6
    eqid
    @11
    @7
    eqid
    ply1plusg
    3eqtr4g
end
