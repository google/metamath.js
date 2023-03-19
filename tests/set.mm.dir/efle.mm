include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "ce.mm"
include "cfv.mm"
include "cle.mm"
include "wb.mm"
include "eflt.mm"
include "ancoms.mm"
include "notbid.mm"
include "lenlt.mm"
include "reefcl.mm"
include "syl2an.mm"
include "3bitr4d.mm"

theorem efle
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> ( exp ` A ) <_ ( exp ` B ) ) )

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
    cB
    cA
    clt
    wbr
    #
    wn
    cB
    ce
    cfv
    #
    cA
    ce
    cfv
    #
    clt
    wbr
    #
    wn
    #
    cA
    cB
    cle
    wbr
    @5
    @4
    cle
    wbr
    #
    @2
    @3
    @6
    @1
    @0
    @3
    @6
    wb
    cB
    cA
    eflt
    ancoms
    notbid
    cA
    cB
    lenlt
    @0
    @5
    cr
    wcel
    @4
    cr
    wcel
    @8
    @7
    wb
    @1
    cA
    reefcl
    cB
    reefcl
    @5
    @4
    lenlt
    syl2an
    3bitr4d
end
