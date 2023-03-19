include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cen.mm"
include "brdom.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "cvv.mm"
include "wcel.mm"
include "wf1o.mm"
include "cuni.mm"
include "cres.mm"
include "ccnv.mm"
include "cdif.mm"
include "cun.mm"
include "vex.mm"
include "resex.mm"
include "cnvex.mm"
include "unex.mm"
include "eqeltri.mm"
include "sbthlem9.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem sbthlem10
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }
  assume sbthlem.3: |- H = ( ( f |` U. D ) u. ( `' g |` ( A \ U. D ) ) )
  assume sbthlem.4: |- B e. _V

  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B f
  disjoint B g
  disjoint H x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ( A ~<_ B /\ B ~<_ A ) -> A ~~ B )

  proof
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    cB
    cA
    vg
    cv
    #
    wf1
    #
    wa
    #
    vg
    wex
    vf
    wex
    #
    cA
    cB
    cen
    wbr
    #
    @2
    @4
    vf
    wex
    #
    @6
    vg
    wex
    #
    wa
    @8
    @0
    @10
    @1
    @11
    cA
    cB
    vf
    sbthlem.4
    brdom
    cB
    cA
    vg
    sbthlem.1
    brdom
    anbi12i
    @4
    @6
    vf
    vg
    eeanv
    bitr4i
    @7
    @9
    vf
    vg
    @7
    cH
    cvv
    wcel
    cA
    cB
    cH
    wf1o
    @9
    cH
    @3
    cD
    cuni
    #
    cres
    #
    @5
    ccnv
    #
    cA
    @12
    cdif
    #
    cres
    #
    cun
    cvv
    sbthlem.3
    @13
    @16
    @3
    @12
    vf
    vex
    resex
    @14
    @15
    @5
    vg
    vex
    cnvex
    resex
    unex
    eqeltri
    vx
    cA
    cB
    cD
    vf
    vg
    cH
    sbthlem.1
    sbthlem.2
    sbthlem.3
    sbthlem9
    cA
    cB
    cH
    cvv
    f1oen3g
    sylancr
    exlimivv
    sylbi
end
