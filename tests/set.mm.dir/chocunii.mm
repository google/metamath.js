include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "csh.mm"
include "chshii.mm"
include "a1i.mm"
include "shocsh.mm"
include "mp1i.mm"
include "cin.mm"
include "c0h.mm"
include "ocin.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "eqtr2.mm"
include "adantl.mm"
include "shuni.mm"
include "ex.mm"

theorem chocunii
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cH: class H
  assume chocuni.1: |- H e. CH


  assert |- ( ( ( A e. H /\ B e. ( _|_ ` H ) ) /\ ( C e. H /\ D e. ( _|_ ` H ) ) ) -> ( ( R = ( A +h B ) /\ R = ( C +h D ) ) -> ( A = C /\ B = D ) ) )

  proof
    cA
    cH
    wcel
    #
    cB
    cH
    cort
    cfv
    #
    wcel
    #
    wa
    #
    cC
    cH
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    wa
    #
    cR
    cA
    cB
    cva
    co
    #
    wceq
    cR
    cC
    cD
    cva
    co
    #
    wceq
    wa
    #
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    @7
    @10
    wa
    #
    cA
    cB
    cC
    cD
    cH
    @1
    cH
    csh
    wcel
    #
    @11
    cH
    chocuni.1
    chshii
    #
    a1i
    @12
    @1
    csh
    wcel
    @11
    @13
    cH
    shocsh
    mp1i
    @12
    cH
    @1
    cin
    c0h
    wceq
    @11
    @13
    cH
    ocin
    mp1i
    @0
    @2
    @6
    @10
    simplll
    @0
    @2
    @6
    @10
    simpllr
    @3
    @4
    @5
    @10
    simplrl
    @3
    @4
    @5
    @10
    simplrr
    @10
    @8
    @9
    wceq
    @7
    cR
    @8
    @9
    eqtr2
    adantl
    shuni
    ex
end
