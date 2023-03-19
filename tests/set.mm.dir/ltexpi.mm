include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "com.mm"
include "wrex.mm"
include "clti.mm"
include "wbr.mm"
include "cpli.mm"
include "wb.mm"
include "pinn.mm"
include "nnaordex.mm"
include "syl2an.mm"
include "ltpiord.mm"
include "addpiord.mm"
include "eqeq1d.mm"
include "pm5.32da.mm"
include "elni2.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "syl6bb.mm"
include "rexbidv2.mm"
include "adantr.mm"
include "3bitr4d.mm"

theorem ltexpi
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. N. /\ B e. N. ) -> ( A <N B <-> E. x e. N. ( A +N x ) = B ) )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    cA
    cB
    wcel
    #
    c0
    vx
    cv
    #
    wcel
    #
    cA
    @3
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    vx
    com
    wrex
    #
    cA
    cB
    clti
    wbr
    cA
    @3
    cpli
    co
    #
    cB
    wceq
    #
    vx
    cnpi
    wrex
    #
    @0
    cA
    com
    wcel
    cB
    com
    wcel
    @2
    @8
    wb
    @1
    cA
    pinn
    cB
    pinn
    vx
    cA
    cB
    nnaordex
    syl2an
    cA
    cB
    ltpiord
    @0
    @11
    @8
    wb
    @1
    @0
    @10
    @7
    vx
    cnpi
    com
    @0
    @3
    cnpi
    wcel
    #
    @10
    wa
    @12
    @6
    wa
    #
    @3
    com
    wcel
    #
    @7
    wa
    #
    @0
    @12
    @10
    @6
    @0
    @12
    wa
    @9
    @5
    cB
    cA
    @3
    addpiord
    eqeq1d
    pm5.32da
    @13
    @14
    @4
    wa
    #
    @6
    wa
    @15
    @12
    @16
    @6
    @3
    elni2
    anbi1i
    @14
    @4
    @6
    anass
    bitri
    syl6bb
    rexbidv2
    adantr
    3bitr4d
end
