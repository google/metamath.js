include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "lesubadd.mm"
include "simp2.mm"
include "recnd.mm"
include "simp3.mm"
include "addcomd.mm"
include "breq2d.mm"
include "bitr4d.mm"

theorem lesubadd2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A - B ) <_ C <-> A <_ ( B + C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    cmin
    co
    cC
    cle
    wbr
    cA
    cC
    cB
    caddc
    co
    #
    cle
    wbr
    cA
    cB
    cC
    caddc
    co
    #
    cle
    wbr
    cA
    cB
    cC
    lesubadd
    @3
    @5
    @4
    cA
    cle
    @3
    cB
    cC
    @3
    cB
    @0
    @1
    @2
    simp2
    recnd
    @3
    cC
    @0
    @1
    @2
    simp3
    recnd
    addcomd
    breq2d
    bitr4d
end
