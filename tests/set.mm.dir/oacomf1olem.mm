include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wf1o.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "wf1.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "cmpt.mm"
include "cres.mm"
include "wss.mm"
include "oaf1o.mm"
include "adantl.mm"
include "f1of1.mm"
include "syl.mm"
include "onss.mm"
include "adantr.mm"
include "f1ssres.mm"
include "syl2anc.mm"
include "wb.mm"
include "resmptd.mm"
include "syl6eqr.mm"
include "f1eq1.mm"
include "mpbid.mm"
include "f1f1orn.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "difss2d.mm"
include "reldisj.mm"
include "mpbird.mm"
include "jca.mm"

theorem oacomf1olem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume oacomf1olem.1: |- F = ( x e. A |-> ( B +o x ) )

  disjoint A x
  disjoint B x
  assert |- ( ( A e. On /\ B e. On ) -> ( F : A -1-1-onto-> ran F /\ ( ran F i^i B ) = (/) ) )

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
    cF
    crn
    #
    cF
    wf1o
    #
    @3
    cB
    cin
    c0
    wceq
    #
    @2
    cA
    con0
    cB
    cdif
    #
    cF
    wf1
    #
    @4
    @2
    cA
    @6
    vx
    con0
    cB
    vx
    cv
    coa
    co
    #
    cmpt
    #
    cA
    cres
    #
    wf1
    #
    @7
    @2
    con0
    @6
    @9
    wf1
    #
    cA
    con0
    wss
    #
    @11
    @2
    con0
    @6
    @9
    wf1o
    #
    @12
    @1
    @14
    @0
    vx
    cB
    oaf1o
    adantl
    con0
    @6
    @9
    f1of1
    syl
    @0
    @13
    @1
    cA
    onss
    adantr
    #
    con0
    @6
    cA
    @9
    f1ssres
    syl2anc
    @2
    @10
    cF
    wceq
    @11
    @7
    wb
    @2
    @10
    vx
    cA
    @8
    cmpt
    cF
    @2
    vx
    con0
    cA
    @8
    @15
    resmptd
    oacomf1olem.1
    syl6eqr
    cA
    @6
    @10
    cF
    f1eq1
    syl
    mpbid
    #
    cA
    @6
    cF
    f1f1orn
    syl
    @2
    @5
    @3
    @6
    wss
    #
    @2
    @7
    cA
    @6
    cF
    wf
    @17
    @16
    cA
    @6
    cF
    f1f
    cA
    @6
    cF
    frn
    3syl
    #
    @2
    @3
    con0
    wss
    @5
    @17
    wb
    @2
    @3
    con0
    cB
    @18
    difss2d
    @3
    cB
    con0
    reldisj
    syl
    mpbird
    jca
end
