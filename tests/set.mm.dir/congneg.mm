include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "congsym.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "neg2sub.mm"
include "syl2an.mm"
include "ad2ant2lr.mm"
include "breqtrrd.mm"

theorem congneg
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) ) -> A || ( -u B - -u C ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    cC
    cz
    wcel
    #
    cA
    cB
    cC
    cmin
    co
    cdvds
    wbr
    #
    wa
    wa
    cA
    cC
    cB
    cmin
    co
    #
    cB
    cneg
    cC
    cneg
    cmin
    co
    #
    cdvds
    cA
    cB
    cC
    congsym
    @1
    @2
    @5
    @4
    wceq
    #
    @0
    @3
    @1
    cB
    cc
    wcel
    cC
    cc
    wcel
    @6
    @2
    cB
    zcn
    cC
    zcn
    cB
    cC
    neg2sub
    syl2an
    ad2ant2lr
    breqtrrd
end
