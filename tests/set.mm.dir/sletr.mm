include "csur.mm"
include "wcel.mm"
include "w3a.mm"
include "csle.mm"
include "wbr.mm"
include "cslt.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "sltletr.mm"
include "3coml.mm"
include "expcomd.mm"
include "imp.mm"
include "con3d.mm"
include "expimpd.mm"
include "wb.mm"
include "slenlt.mm"
include "3adant1.mm"
include "anbi2d.mm"
include "3adant2.mm"
include "3imtr4d.mm"

theorem sletr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. No /\ B e. No /\ C e. No ) -> ( ( A <_s B /\ B <_s C ) -> A <_s C ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cC
    csur
    wcel
    #
    w3a
    #
    cA
    cB
    csle
    wbr
    #
    cC
    cB
    cslt
    wbr
    #
    wn
    #
    wa
    cC
    cA
    cslt
    wbr
    #
    wn
    #
    @4
    cB
    cC
    csle
    wbr
    #
    wa
    cA
    cC
    csle
    wbr
    #
    @3
    @4
    @6
    @8
    @3
    @4
    wa
    @7
    @5
    @3
    @4
    @7
    @5
    wi
    @3
    @7
    @4
    @5
    @2
    @0
    @1
    @7
    @4
    wa
    @5
    wi
    cC
    cA
    cB
    sltletr
    3coml
    expcomd
    imp
    con3d
    expimpd
    @3
    @9
    @6
    @4
    @1
    @2
    @9
    @6
    wb
    @0
    cB
    cC
    slenlt
    3adant1
    anbi2d
    @0
    @2
    @10
    @8
    wb
    @1
    cA
    cC
    slenlt
    3adant2
    3imtr4d
end
