include "c1o.mm"
include "cdif.mm"
include "c2o.mm"
include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "elpri.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "difid.mm"
include "orim12i.mm"
include "orcomd.mm"
include "syl.mm"
include "con0.mm"
include "cvv.mm"
include "1on.mm"
include "difexg.mm"
include "ax-mp.mm"
include "elpr.mm"
include "sylibr.mm"
include "df2o3.mm"
include "syl6eleqr.mm"
include "eleq2s.mm"

theorem 2oconcl
  let cA: class A


  assert |- ( A e. 2o -> ( 1o \ A ) e. 2o )

  proof
    c1o
    cA
    cdif
    #
    c2o
    wcel
    cA
    c0
    c1o
    cpr
    #
    c2o
    cA
    @1
    wcel
    #
    @0
    @1
    c2o
    @2
    @0
    c0
    wceq
    #
    @0
    c1o
    wceq
    #
    wo
    #
    @0
    @1
    wcel
    @2
    cA
    c0
    wceq
    #
    cA
    c1o
    wceq
    #
    wo
    #
    @5
    cA
    c0
    c1o
    elpri
    @8
    @4
    @3
    @6
    @4
    @7
    @3
    @6
    @0
    c1o
    c0
    cdif
    c1o
    cA
    c0
    c1o
    difeq2
    c1o
    dif0
    syl6eq
    @7
    @0
    c1o
    c1o
    cdif
    c0
    cA
    c1o
    c1o
    difeq2
    c1o
    difid
    syl6eq
    orim12i
    orcomd
    syl
    @0
    c0
    c1o
    c1o
    con0
    wcel
    @0
    cvv
    wcel
    1on
    c1o
    cA
    con0
    difexg
    ax-mp
    elpr
    sylibr
    df2o3
    syl6eleqr
    df2o3
    eleq2s
end
