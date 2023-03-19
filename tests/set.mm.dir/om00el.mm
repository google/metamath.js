include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "om00.mm"
include "necon3abid.mm"
include "wb.mm"
include "omcl.mm"
include "on0eln0.mm"
include "syl.mm"
include "bi2anan9.mm"
include "neanior.mm"
include "syl6bb.mm"
include "3bitr4d.mm"

theorem om00el
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( (/) e. ( A .o B ) <-> ( (/) e. A /\ (/) e. B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    comu
    co
    #
    c0
    wne
    #
    cA
    c0
    wceq
    cB
    c0
    wceq
    wo
    #
    wn
    #
    c0
    @3
    wcel
    #
    c0
    cA
    wcel
    #
    c0
    cB
    wcel
    #
    wa
    #
    @2
    @5
    @3
    c0
    cA
    cB
    om00
    necon3abid
    @2
    @3
    con0
    wcel
    @7
    @4
    wb
    cA
    cB
    omcl
    @3
    on0eln0
    syl
    @2
    @10
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    @6
    @0
    @8
    @11
    @1
    @9
    @12
    cA
    on0eln0
    cB
    on0eln0
    bi2anan9
    cA
    c0
    cB
    c0
    neanior
    syl6bb
    3bitr4d
end
