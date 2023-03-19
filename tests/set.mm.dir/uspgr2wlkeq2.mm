include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cwlks.mm"
include "cfv.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "w3a.mm"
include "c2nd.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "simpr.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "fveq1.mm"
include "adantl.mm"
include "ralrimivw.mm"
include "wb.mm"
include "simpl1l.mm"
include "simpl.mm"
include "anim12i.mm"
include "3adant1.mm"
include "3ad2ant2.mm"
include "uspgr2wlkeq.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "ex.mm"

theorem uspgr2wlkeq2
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let vi: setvar i


  assert |- ( ( ( G e. USPGraph /\ N e. NN0 ) /\ ( A e. ( Walks ` G ) /\ ( # ` ( 1st ` A ) ) = N ) /\ ( B e. ( Walks ` G ) /\ ( # ` ( 1st ` B ) ) = N ) ) -> ( ( 2nd ` A ) = ( 2nd ` B ) -> A = B ) )

  proof
    cG
    cuspgr
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cG
    cwlks
    cfv
    #
    wcel
    #
    cA
    c1st
    cfv
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cB
    @3
    wcel
    #
    cB
    c1st
    cfv
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    w3a
    #
    cA
    c2nd
    cfv
    #
    cB
    c2nd
    cfv
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @12
    @15
    wa
    #
    @16
    cN
    @9
    wceq
    #
    vi
    cv
    #
    @13
    cfv
    @19
    @14
    cfv
    wceq
    #
    vi
    cc0
    cN
    cfz
    co
    #
    wral
    #
    @12
    @18
    @15
    @11
    @2
    @18
    @7
    @11
    @9
    cN
    @8
    @10
    simpr
    eqcomd
    3ad2ant3
    adantr
    @17
    @20
    vi
    @21
    @15
    @20
    @12
    @19
    @13
    @14
    fveq1
    adantl
    ralrimivw
    @17
    @0
    @4
    @8
    wa
    #
    cN
    @5
    wceq
    #
    @16
    @18
    @22
    wa
    wb
    @0
    @1
    @7
    @11
    @15
    simpl1l
    @12
    @23
    @15
    @7
    @11
    @23
    @2
    @7
    @4
    @11
    @8
    @4
    @6
    simpl
    @8
    @10
    simpl
    anim12i
    3adant1
    adantr
    @12
    @24
    @15
    @7
    @2
    @24
    @11
    @7
    @5
    cN
    @4
    @6
    simpr
    eqcomd
    3ad2ant2
    adantr
    vi
    cA
    cB
    cG
    cN
    uspgr2wlkeq
    syl3anc
    mpbir2and
    ex
end
