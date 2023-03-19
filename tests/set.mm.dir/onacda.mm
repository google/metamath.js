include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "coa.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "enrefg.mm"
include "adantr.mm"
include "wf1o.mm"
include "simpr.mm"
include "eqid.mm"
include "oacomf1olem.mm"
include "ancoms.mm"
include "simpld.mm"
include "f1oeng.mm"
include "syl2anc.mm"
include "incom.mm"
include "simprd.mm"
include "syl5eq.mm"
include "cdaenun.mm"
include "syl3anc.mm"
include "oarec.mm"
include "breqtrrd.mm"
include "ensymd.mm"

theorem onacda
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. On ) -> ( A +o B ) ~~ ( A +c B ) )

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
    ccda
    co
    #
    cA
    cB
    coa
    co
    #
    @2
    @3
    cA
    vx
    cB
    cA
    vx
    cv
    coa
    co
    cmpt
    #
    crn
    #
    cun
    #
    @4
    cen
    @2
    cA
    cA
    cen
    wbr
    #
    cB
    @6
    cen
    wbr
    #
    cA
    @6
    cin
    #
    c0
    wceq
    @3
    @7
    cen
    wbr
    @0
    @8
    @1
    cA
    con0
    enrefg
    adantr
    @2
    @1
    cB
    @6
    @5
    wf1o
    #
    @9
    @0
    @1
    simpr
    @2
    @11
    @6
    cA
    cin
    #
    c0
    wceq
    #
    @1
    @0
    @11
    @13
    wa
    vx
    cB
    cA
    @5
    @5
    eqid
    oacomf1olem
    ancoms
    #
    simpld
    cB
    @6
    con0
    @5
    f1oeng
    syl2anc
    @2
    @10
    @12
    c0
    cA
    @6
    incom
    @2
    @11
    @13
    @14
    simprd
    syl5eq
    cA
    cA
    cB
    @6
    cdaenun
    syl3anc
    vx
    cA
    cB
    oarec
    breqtrrd
    ensymd
end
