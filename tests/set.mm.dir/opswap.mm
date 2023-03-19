include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "cuni.mm"
include "wceq.mm"
include "cnvsng.mm"
include "unieqd.mm"
include "opex.mm"
include "unisn.mm"
include "syl6eq.mm"
include "wn.mm"
include "c0.mm"
include "uni0.mm"
include "opprc.mm"
include "sneqd.mm"
include "cnveqd.mm"
include "cnvsn0.mm"
include "ancom.mm"
include "sylnbi.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem opswap
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- U. `' { <. A , B >. } = <. B , A >.

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    cB
    cop
    #
    csn
    #
    ccnv
    #
    cuni
    #
    cB
    cA
    cop
    #
    wceq
    @2
    @6
    @7
    csn
    #
    cuni
    @7
    @2
    @5
    @8
    cA
    cB
    cvv
    cvv
    cnvsng
    unieqd
    @7
    cB
    cA
    opex
    unisn
    syl6eq
    @2
    wn
    #
    c0
    cuni
    c0
    @6
    @7
    uni0
    @9
    @5
    c0
    @9
    @5
    c0
    csn
    #
    ccnv
    c0
    @9
    @4
    @10
    @9
    @3
    c0
    cA
    cB
    opprc
    sneqd
    cnveqd
    cnvsn0
    syl6eq
    unieqd
    @2
    @1
    @0
    wa
    @7
    c0
    wceq
    @0
    @1
    ancom
    cB
    cA
    opprc
    sylnbi
    3eqtr4a
    pm2.61i
end
