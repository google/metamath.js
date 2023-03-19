include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "ce.mm"
include "cfv.mm"
include "wceq.mm"
include "efle.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "letri3.mm"
include "reefcl.mm"
include "syl2an.mm"
include "3bitr4rd.mm"

theorem reef11
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( exp ` A ) = ( exp ` B ) <-> A = B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wa
    cA
    ce
    cfv
    #
    cB
    ce
    cfv
    #
    cle
    wbr
    #
    @6
    @5
    cle
    wbr
    #
    wa
    #
    cA
    cB
    wceq
    @5
    @6
    wceq
    #
    @2
    @3
    @7
    @4
    @8
    cA
    cB
    efle
    @1
    @0
    @4
    @8
    wb
    cB
    cA
    efle
    ancoms
    anbi12d
    cA
    cB
    letri3
    @0
    @5
    cr
    wcel
    @6
    cr
    wcel
    @10
    @9
    wb
    @1
    cA
    reefcl
    cB
    reefcl
    @5
    @6
    letri3
    syl2an
    3bitr4rd
end
