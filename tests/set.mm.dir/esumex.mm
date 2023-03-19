include "cesum.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cvv.mm"
include "df-esum.mm"
include "ovex.mm"
include "uniex.mm"
include "eqeltri.mm"

theorem esumex
  let cA: class A
  let cB: class B
  let vk: setvar k


  assert |- sum* k e. A B e. _V

  proof
    cA
    cB
    vk
    cesum
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    cuni
    cvv
    cA
    cB
    vk
    df-esum
    @2
    @0
    @1
    ctsu
    ovex
    uniex
    eqeltri
end
