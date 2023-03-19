include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "cun.mm"
include "cdom.mm"
include "wbr.mm"
include "cdanum.mm"
include "uncdadom.mm"
include "numdom.mm"
include "syl2anc.mm"

theorem unnum
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( A u. B ) e. dom card )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @0
    wcel
    wa
    cA
    cB
    ccda
    co
    #
    @0
    wcel
    cA
    cB
    cun
    #
    @1
    cdom
    wbr
    @2
    @0
    wcel
    cA
    cB
    cdanum
    cA
    cB
    @0
    @0
    uncdadom
    @1
    @2
    numdom
    syl2anc
end
