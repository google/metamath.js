include "cgic.mm"
include "wbr.mm"
include "cgim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cen.mm"
include "brgic.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "wf1o.mm"
include "gimf1o.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "f1oen.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem gicen
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let cT: class T
  assume gicen.b: |- B = ( Base ` R )
  assume gicen.c: |- C = ( Base ` S )


  assert |- ( R ~=g S -> B ~~ C )

  proof
    cR
    cS
    cgic
    wbr
    cR
    cS
    cgim
    co
    #
    c0
    wne
    #
    cB
    cC
    cen
    wbr
    #
    cR
    cS
    brgic
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    n0
    @4
    @2
    vf
    @4
    cB
    cC
    @3
    wf1o
    @2
    cB
    cC
    cR
    cS
    @3
    gicen.b
    gicen.c
    gimf1o
    cB
    cC
    @3
    cB
    cR
    cbs
    cfv
    cvv
    gicen.b
    cR
    cbs
    fvex
    eqeltri
    f1oen
    syl
    exlimiv
    sylbi
    sylbi
end
