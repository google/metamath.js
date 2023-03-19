include "con0.mm"
include "wcel.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ciin.mm"
include "cmpt.mm"
include "crn.mm"
include "cint.mm"
include "wceq.mm"
include "dfiin3g.mm"
include "adantr.mm"
include "wss.mm"
include "eqid.mm"
include "rnmptss.mm"
include "cdm.mm"
include "dm0rn0.mm"
include "dmmptg.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "oninton.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem iinon
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( ( A. x e. A B e. On /\ A =/= (/) ) -> |^|_ x e. A B e. On )

  proof
    cB
    con0
    wcel
    vx
    cA
    wral
    #
    cA
    c0
    wne
    #
    wa
    #
    vx
    cA
    cB
    ciin
    #
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cint
    #
    con0
    @0
    @3
    @6
    wceq
    @1
    vx
    cA
    cB
    con0
    dfiin3g
    adantr
    @2
    @5
    con0
    wss
    #
    @5
    c0
    wne
    #
    @6
    con0
    wcel
    @0
    @7
    @1
    vx
    cA
    cB
    con0
    @4
    @4
    eqid
    rnmptss
    adantr
    @0
    @8
    @1
    @0
    @5
    c0
    cA
    c0
    @5
    c0
    wceq
    @4
    cdm
    #
    c0
    wceq
    @0
    cA
    c0
    wceq
    @4
    dm0rn0
    @0
    @9
    cA
    c0
    vx
    cA
    cB
    con0
    dmmptg
    eqeq1d
    syl5bbr
    necon3bid
    biimpar
    @5
    oninton
    syl2anc
    eqeltrd
end
