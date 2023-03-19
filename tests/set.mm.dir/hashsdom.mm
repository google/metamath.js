include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "csdm.mm"
include "cle.mm"
include "wne.mm"
include "cn0.mm"
include "wb.mm"
include "hashcl.mm"
include "cr.mm"
include "nn0re.mm"
include "ltlen.mm"
include "syl2an.mm"
include "hashdom.mm"
include "wceq.mm"
include "eqcom.mm"
include "hashen.mm"
include "syl5bb.mm"
include "necon3abid.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "brsdom.mm"
include "syl6bbr.mm"

theorem hashsdom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( ( # ` A ) < ( # ` B ) <-> A ~< B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    clt
    wbr
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wn
    #
    wa
    #
    cA
    cB
    csdm
    wbr
    @2
    @5
    @3
    @4
    cle
    wbr
    #
    @4
    @3
    wne
    #
    wa
    #
    @9
    @0
    @3
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    @5
    @12
    wb
    #
    @1
    cA
    hashcl
    cB
    hashcl
    @13
    @3
    cr
    wcel
    @4
    cr
    wcel
    @15
    @14
    @3
    nn0re
    @4
    nn0re
    @3
    @4
    ltlen
    syl2an
    syl2an
    @2
    @10
    @6
    @11
    @8
    cA
    cB
    cfn
    hashdom
    @2
    @7
    @4
    @3
    @4
    @3
    wceq
    @3
    @4
    wceq
    @2
    @7
    @4
    @3
    eqcom
    cA
    cB
    hashen
    syl5bb
    necon3abid
    anbi12d
    bitrd
    cA
    cB
    brsdom
    syl6bbr
end
