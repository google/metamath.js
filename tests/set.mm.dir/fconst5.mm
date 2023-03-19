include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "crn.mm"
include "wi.mm"
include "rneq.mm"
include "rnxp.mm"
include "eqeq2d.mm"
include "syl5ib.mm"
include "adantl.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "wfo.mm"
include "df-fo.mm"
include "fof.mm"
include "sylbir.mm"
include "fconst2g.mm"
include "expd.mm"
include "adantrd.mm"
include "wn.mm"
include "wrel.mm"
include "fnrel.mm"
include "snprc.mm"
include "relrn0.mm"
include "biimprd.mm"
include "wb.mm"
include "eqeq2.mm"
include "adantr.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "3imtr4d.mm"
include "ex.mm"
include "sylbi.mm"
include "syl5.mm"
include "pm2.61i.mm"
include "impbid.mm"

theorem fconst5
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ A =/= (/) ) -> ( F = ( A X. { B } ) <-> ran F = { B } ) )

  proof
    cF
    cA
    wfn
    #
    cA
    c0
    wne
    #
    wa
    #
    cF
    cA
    cB
    csn
    #
    cxp
    #
    wceq
    #
    cF
    crn
    #
    @3
    wceq
    #
    @1
    @5
    @7
    wi
    @0
    @5
    @6
    @4
    crn
    #
    wceq
    @1
    @7
    cF
    @4
    rneq
    @1
    @8
    @3
    @6
    cA
    @3
    rnxp
    eqeq2d
    syl5ib
    adantl
    cB
    cvv
    wcel
    #
    @2
    @7
    @5
    wi
    #
    wi
    @9
    @0
    @10
    @1
    @9
    @0
    @7
    @5
    @0
    @7
    wa
    #
    cA
    @3
    cF
    wf
    #
    @9
    @5
    @11
    cA
    @3
    cF
    wfo
    @12
    cA
    @3
    cF
    df-fo
    cA
    @3
    cF
    fof
    sylbir
    cA
    cB
    cvv
    cF
    fconst2g
    syl5ib
    expd
    adantrd
    @9
    wn
    #
    @0
    @10
    @1
    @0
    cF
    wrel
    #
    @13
    @10
    cA
    cF
    fnrel
    @13
    @3
    c0
    wceq
    #
    @14
    @10
    wi
    cB
    snprc
    @15
    @14
    @10
    @15
    @14
    wa
    @6
    c0
    wceq
    #
    cF
    c0
    wceq
    #
    @7
    @5
    @14
    @16
    @17
    wi
    @15
    @14
    @17
    @16
    cF
    relrn0
    biimprd
    adantl
    @15
    @7
    @16
    wb
    @14
    @3
    c0
    @6
    eqeq2
    adantr
    @15
    @5
    @17
    wb
    @14
    @15
    @4
    c0
    cF
    @15
    @4
    cA
    c0
    cxp
    c0
    @3
    c0
    cA
    xpeq2
    cA
    xp0
    syl6eq
    eqeq2d
    adantr
    3imtr4d
    ex
    sylbi
    syl5
    adantrd
    pm2.61i
    impbid
end
