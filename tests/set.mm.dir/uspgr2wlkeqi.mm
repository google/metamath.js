include "cuspgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wa.mm"
include "c2nd.mm"
include "wceq.mm"
include "w3a.mm"
include "c1st.mm"
include "chash.mm"
include "cn0.mm"
include "wbr.mm"
include "wi.mm"
include "wlkcpr.mm"
include "wlkcl.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wb.mm"
include "wlklenvm1.mm"
include "eqeqan12rd.mm"
include "adantr.mm"
include "mpbird.mm"
include "anim2i.mm"
include "exp44.mm"
include "mpcom.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "imp31.mm"
include "3adant1.mm"
include "simpl.mm"
include "anim12i.mm"
include "eqidd.mm"
include "simpr.mm"
include "uspgr2wlkeq2.mm"
include "syl3anc.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "mpd.mm"

theorem uspgr2wlkeqi
  let cA: class A
  let cB: class B
  let cG: class G
  let vi: setvar i
  let cN: class N


  assert |- ( ( G e. USPGraph /\ ( A e. ( Walks ` G ) /\ B e. ( Walks ` G ) ) /\ ( 2nd ` A ) = ( 2nd ` B ) ) -> A = B )

  proof
    cG
    cuspgr
    wcel
    #
    cA
    cG
    cwlks
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
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
    w3a
    cA
    c1st
    cfv
    #
    chash
    cfv
    #
    cn0
    wcel
    #
    cB
    c1st
    cfv
    #
    chash
    cfv
    #
    @9
    wceq
    #
    wa
    #
    cA
    cB
    wceq
    #
    @4
    @7
    @14
    @0
    @2
    @3
    @7
    @14
    @2
    @8
    @5
    @1
    wbr
    #
    @3
    @7
    @14
    wi
    #
    wi
    cG
    cA
    wlkcpr
    @3
    @11
    @6
    @1
    wbr
    #
    @16
    @17
    cG
    cB
    wlkcpr
    @10
    @16
    @18
    @17
    wi
    @5
    @8
    cG
    wlkcl
    @10
    @16
    @18
    @7
    @14
    @16
    @18
    wa
    #
    @7
    wa
    #
    @13
    @10
    @20
    @13
    @6
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @5
    chash
    cfv
    #
    c1
    cmin
    co
    #
    wceq
    #
    @7
    @25
    @19
    @7
    @24
    @22
    @7
    @23
    @21
    c1
    cmin
    @5
    @6
    chash
    fveq2
    oveq1d
    eqcomd
    adantl
    @19
    @13
    @25
    wb
    @7
    @18
    @16
    @12
    @22
    @9
    @24
    @6
    @11
    cG
    wlklenvm1
    @5
    @8
    cG
    wlklenvm1
    eqeqan12rd
    adantr
    mpbird
    anim2i
    exp44
    mpcom
    syl5bi
    sylbi
    imp31
    3adant1
    @0
    @4
    @7
    @14
    @15
    wi
    @0
    @4
    wa
    #
    @14
    @7
    @15
    @26
    @14
    @7
    @15
    wi
    #
    @26
    @14
    wa
    @0
    @10
    wa
    @2
    @9
    @9
    wceq
    #
    wa
    @3
    @13
    wa
    @27
    @26
    @0
    @14
    @10
    @0
    @4
    simpl
    @10
    @13
    simpl
    anim12i
    @26
    @2
    @14
    @28
    @4
    @2
    @0
    @2
    @3
    simpl
    adantl
    @14
    @9
    eqidd
    anim12i
    @26
    @3
    @14
    @13
    @4
    @3
    @0
    @2
    @3
    simpr
    adantl
    @10
    @13
    simpr
    anim12i
    cA
    cB
    cG
    @9
    uspgr2wlkeq2
    syl3anc
    ex
    com23
    3impia
    mpd
end
