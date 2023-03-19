include "wcel.mm"
include "c2o.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "c1o.mm"
include "wo.mm"
include "wa.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "xpsc0.mm"
include "adantr.mm"
include "fveq2.mm"
include "iftrue.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "xpsc1.mm"
include "adantl.mm"
include "wne.mm"
include "1n0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "syl.mm"
include "jaod.mm"
include "syl5.mm"
include "3impia.mm"

theorem xpscfv
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ C e. 2o ) -> ( `' ( { A } +c { B } ) ` C ) = if ( C = (/) , A , B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    c2o
    wcel
    #
    cC
    cA
    csn
    cB
    csn
    ccda
    co
    ccnv
    #
    cfv
    #
    cC
    c0
    wceq
    #
    cA
    cB
    cif
    #
    wceq
    #
    @2
    @5
    cC
    c1o
    wceq
    #
    wo
    #
    @0
    @1
    wa
    #
    @7
    @9
    cC
    c0
    c1o
    cpr
    c2o
    cC
    c0
    c1o
    elpri
    df2o3
    eleq2s
    @10
    @5
    @7
    @8
    @10
    @7
    @5
    c0
    @3
    cfv
    #
    cA
    wceq
    #
    @0
    @12
    @1
    cA
    cB
    cV
    xpsc0
    adantr
    @5
    @4
    @11
    @6
    cA
    cC
    c0
    @3
    fveq2
    @5
    cA
    cB
    iftrue
    eqeq12d
    syl5ibrcom
    @10
    @7
    @8
    c1o
    @3
    cfv
    #
    cB
    wceq
    #
    @1
    @14
    @0
    cA
    cB
    cW
    xpsc1
    adantl
    @8
    @4
    @13
    @6
    cB
    cC
    c1o
    @3
    fveq2
    @8
    cC
    c0
    wne
    #
    @6
    cB
    wceq
    @8
    @15
    c1o
    c0
    wne
    1n0
    cC
    c1o
    c0
    neeq1
    mpbiri
    cC
    c0
    cA
    cB
    ifnefalse
    syl
    eqeq12d
    syl5ibrcom
    jaod
    syl5
    3impia
end
