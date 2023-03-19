include "csur.mm"
include "wcel.mm"
include "w3a.mm"
include "csle.mm"
include "wbr.mm"
include "cslt.mm"
include "wa.mm"
include "wn.mm"
include "wb.mm"
include "slenlt.mm"
include "3adant3.mm"
include "anbi1d.mm"
include "wor.mm"
include "wi.mm"
include "sltso.mm"
include "sotr2.mm"
include "mpan.mm"
include "sylbid.mm"

theorem slelttr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. No /\ B e. No /\ C e. No ) -> ( ( A <_s B /\ B <s C ) -> A <s C ) )

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
    cB
    cC
    cslt
    wbr
    #
    wa
    cB
    cA
    cslt
    wbr
    wn
    #
    @5
    wa
    #
    cA
    cC
    cslt
    wbr
    #
    @3
    @4
    @6
    @5
    @0
    @1
    @4
    @6
    wb
    @2
    cA
    cB
    slenlt
    3adant3
    anbi1d
    csur
    cslt
    wor
    @3
    @7
    @8
    wi
    sltso
    csur
    cA
    cB
    cC
    cslt
    sotr2
    mpan
    sylbid
end
