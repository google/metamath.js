include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cn.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "cdm.mm"
include "wss.mm"
include "wf1o.mm"
include "nnfoctb.mm"
include "wi.mm"
include "crn.mm"
include "cres.mm"
include "cpw.mm"
include "wrex.mm"
include "clt.mm"
include "cvv.mm"
include "fofn.mm"
include "wcel.mm"
include "nnex.mm"
include "a1i.mm"
include "wwe.mm"
include "ltwenn.mm"
include "wessf1orn.mm"
include "w3a.mm"
include "wceq.mm"
include "f1odm.mm"
include "adantl.mm"
include "elpwi.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "3adant1.mm"
include "simpr.mm"
include "eqidd.mm"
include "eqcomd.mm"
include "forn.mm"
include "f1oeq123d.mm"
include "mpbid.mm"
include "3adant2.mm"
include "vex.mm"
include "resex.mm"
include "dmeq.mm"
include "sseq1d.mm"
include "id.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "exlimdv.mm"

theorem ssnnf1octb
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x

  disjoint A f
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint g x
  assert |- ( ( A ~<_ _om /\ A =/= (/) ) -> E. f ( dom f C_ NN /\ f : dom f -1-1-onto-> A ) )

  proof
    cA
    com
    cdom
    wbr
    cA
    c0
    wne
    wa
    #
    cn
    cA
    vg
    cv
    #
    wfo
    #
    vg
    wex
    vf
    cv
    #
    cdm
    #
    cn
    wss
    #
    @4
    cA
    @3
    wf1o
    #
    wa
    #
    vf
    wex
    #
    cA
    vg
    nnfoctb
    @0
    @2
    @8
    vg
    @2
    @8
    wi
    @0
    @2
    vx
    cv
    #
    @1
    crn
    #
    @1
    @9
    cres
    #
    wf1o
    #
    vx
    cn
    cpw
    #
    wrex
    @8
    @2
    vx
    cn
    clt
    @1
    cvv
    cn
    cA
    @1
    fofn
    cn
    cvv
    wcel
    @2
    nnex
    a1i
    cn
    clt
    wwe
    @2
    ltwenn
    a1i
    wessf1orn
    @2
    @12
    @8
    vx
    @13
    @2
    @9
    @13
    wcel
    #
    @12
    @8
    @2
    @14
    @12
    w3a
    @11
    cdm
    #
    cn
    wss
    #
    @15
    cA
    @11
    wf1o
    #
    @8
    @14
    @12
    @16
    @2
    @14
    @12
    wa
    @15
    @9
    cn
    @12
    @15
    @9
    wceq
    @14
    @9
    @10
    @11
    f1odm
    #
    adantl
    @14
    @9
    cn
    wss
    @12
    @9
    cn
    elpwi
    adantr
    eqsstrd
    3adant1
    @2
    @12
    @17
    @14
    @2
    @12
    wa
    #
    @12
    @17
    @2
    @12
    simpr
    @19
    @9
    @15
    @10
    cA
    @11
    @11
    @19
    @11
    eqidd
    @12
    @9
    @15
    wceq
    @2
    @12
    @15
    @9
    @18
    eqcomd
    adantl
    @2
    @10
    cA
    wceq
    @12
    cn
    cA
    @1
    forn
    adantr
    f1oeq123d
    mpbid
    3adant2
    @7
    @16
    @17
    wa
    vf
    @11
    @1
    @9
    vg
    vex
    resex
    @3
    @11
    wceq
    #
    @5
    @16
    @6
    @17
    @20
    @4
    @15
    cn
    @3
    @11
    dmeq
    #
    sseq1d
    @20
    @4
    @15
    cA
    cA
    @3
    @11
    @20
    id
    @21
    @20
    cA
    eqidd
    f1oeq123d
    anbi12d
    spcev
    syl2anc
    3exp
    rexlimdv
    mpd
    a1i
    exlimdv
    mpd
end
