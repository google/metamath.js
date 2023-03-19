include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "fveq2.mm"
include "c1st.mm"
include "bj-inftyexpiinv.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "sylibd.mm"
include "syl5.mm"
include "impbid2.mm"

theorem bj-inftyexpiinj
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( -u _pi (,] _pi ) /\ B e. ( -u _pi (,] _pi ) ) -> ( A = B <-> ( inftyexpi ` A ) = ( inftyexpi ` B ) ) )

  proof
    cA
    cpi
    cneg
    cpi
    cioc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    cA
    cinftyexpi
    cfv
    #
    cB
    cinftyexpi
    cfv
    #
    wceq
    #
    cA
    cB
    cinftyexpi
    fveq2
    @7
    @5
    c1st
    cfv
    #
    @6
    c1st
    cfv
    #
    wceq
    #
    @3
    @4
    @5
    @6
    c1st
    fveq2
    @3
    @10
    cA
    @9
    wceq
    #
    @4
    @3
    @10
    @11
    @3
    @8
    cA
    @9
    @1
    @8
    cA
    wceq
    @2
    cA
    bj-inftyexpiinv
    adantr
    eqeq1d
    biimpd
    @3
    @9
    cB
    cA
    @2
    @9
    cB
    wceq
    @1
    cB
    bj-inftyexpiinv
    adantl
    eqeq2d
    sylibd
    syl5
    impbid2
end
