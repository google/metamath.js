include "csur.mm"
include "wcel.mm"
include "w3a.mm"
include "cslt.mm"
include "wbr.mm"
include "csle.mm"
include "wa.mm"
include "wn.mm"
include "wb.mm"
include "slenlt.mm"
include "3adant1.mm"
include "anbi2d.mm"
include "wor.mm"
include "wi.mm"
include "sltso.mm"
include "sotr3.mm"
include "mpan.mm"
include "sylbid.mm"

theorem sltletr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. No /\ B e. No /\ C e. No ) -> ( ( A <s B /\ B <_s C ) -> A <s C ) )

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
    cslt
    wbr
    #
    cB
    cC
    csle
    wbr
    #
    wa
    @4
    cC
    cB
    cslt
    wbr
    wn
    #
    wa
    #
    cA
    cC
    cslt
    wbr
    #
    @3
    @5
    @6
    @4
    @1
    @2
    @5
    @6
    wb
    @0
    cB
    cC
    slenlt
    3adant1
    anbi2d
    csur
    cslt
    wor
    @3
    @7
    @8
    wi
    sltso
    csur
    cslt
    cA
    cB
    cC
    sotr3
    mpan
    sylbid
end
