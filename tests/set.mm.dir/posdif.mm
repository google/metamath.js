include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "resubcl.mm"
include "ancoms.mm"
include "simpl.mm"
include "ltaddpos.mm"
include "syl2anc.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "pncan3.mm"
include "syl2an.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem posdif
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> 0 < ( B - A ) ) )

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
    cc0
    cB
    cA
    cmin
    co
    #
    clt
    wbr
    #
    cA
    cA
    @3
    caddc
    co
    #
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    @2
    @3
    cr
    wcel
    #
    @0
    @4
    @6
    wb
    @1
    @0
    @7
    cB
    cA
    resubcl
    ancoms
    @0
    @1
    simpl
    @3
    cA
    ltaddpos
    syl2anc
    @2
    @5
    cB
    cA
    clt
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @5
    cB
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    pncan3
    syl2an
    breq2d
    bitr2d
end
