include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "csuc.mm"
include "cdom.mm"
include "wex.mm"
include "sdomdom.mm"
include "brdomi.mm"
include "syl.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "crn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "adantr.mm"
include "vex.mm"
include "rnex.mm"
include "a1i.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "adantl.mm"
include "f1of1.mm"
include "f1dom2g.mm"
include "syl3anc.mm"
include "wn.mm"
include "cen.mm"
include "sdomnen.mm"
include "wss.mm"
include "ssdif0.mm"
include "simplr.mm"
include "wfn.mm"
include "wf.mm"
include "f1f.mm"
include "df-f.mm"
include "sylib.mm"
include "simprd.mm"
include "simpr.mm"
include "eqssd.mm"
include "dff1o5.mm"
include "sylanbrc.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "ex.mm"
include "syl5bir.mm"
include "mtod.mm"
include "neq0.mm"
include "snssi.mm"
include "en2sn.mm"
include "sylancl.mm"
include "wi.mm"
include "brrelex2i.mm"
include "difexg.mm"
include "ssdomg.mm"
include "3syl.mm"
include "endomtr.mm"
include "syl6an.mm"
include "syl5.mm"
include "exlimdv.mm"
include "mpd.mm"
include "disjdif.mm"
include "undom.mm"
include "syl21anc.mm"
include "df-suc.mm"
include "undif2.mm"
include "ssequn1.mm"
include "syl5req.mm"
include "3brtr4d.mm"
include "exlimddv.mm"

theorem sucdom2
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vw: setvar w


  assert |- ( A ~< B -> suc A ~<_ B )

  proof
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    cA
    csuc
    #
    cB
    cdom
    wbr
    vf
    @0
    cA
    cB
    cdom
    wbr
    @2
    vf
    wex
    cA
    cB
    sdomdom
    cA
    cB
    vf
    brdomi
    syl
    @0
    @2
    wa
    #
    cA
    cA
    csn
    #
    cun
    #
    @1
    crn
    #
    cB
    @7
    cdif
    #
    cun
    #
    @3
    cB
    cdom
    @4
    cA
    @7
    cdom
    wbr
    #
    @5
    @8
    cdom
    wbr
    #
    @7
    @8
    cin
    c0
    wceq
    #
    @6
    @9
    cdom
    wbr
    @4
    cA
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    cA
    @7
    @1
    wf1
    #
    @10
    @0
    @13
    @2
    cA
    cB
    csdm
    relsdom
    brrelexi
    adantr
    #
    @14
    @4
    @1
    vf
    vex
    #
    rnex
    a1i
    @4
    cA
    @7
    @1
    wf1o
    #
    @15
    @2
    @18
    @0
    cA
    cB
    @1
    f1f1orn
    adantl
    cA
    @7
    @1
    f1of1
    syl
    cA
    @7
    @1
    cvv
    cvv
    f1dom2g
    syl3anc
    @4
    vw
    cv
    #
    @8
    wcel
    #
    vw
    wex
    #
    @11
    @4
    @8
    c0
    wceq
    #
    wn
    @21
    @4
    @22
    cA
    cB
    cen
    wbr
    #
    @0
    @23
    wn
    @2
    cA
    cB
    sdomnen
    adantr
    @22
    cB
    @7
    wss
    #
    @4
    @23
    cB
    @7
    ssdif0
    @4
    @24
    @23
    @4
    @24
    wa
    #
    @1
    cvv
    wcel
    cA
    cB
    @1
    wf1o
    #
    @23
    @17
    @25
    @2
    @7
    cB
    wceq
    @26
    @0
    @2
    @24
    simplr
    #
    @25
    @7
    cB
    @25
    @2
    @7
    cB
    wss
    #
    @27
    @2
    @1
    cA
    wfn
    #
    @28
    @2
    cA
    cB
    @1
    wf
    @29
    @28
    wa
    cA
    cB
    @1
    f1f
    cA
    cB
    @1
    df-f
    sylib
    simprd
    #
    syl
    @4
    @24
    simpr
    eqssd
    cA
    cB
    @1
    dff1o5
    sylanbrc
    cA
    cB
    @1
    cvv
    f1oen3g
    sylancr
    ex
    syl5bir
    mtod
    vw
    @8
    neq0
    sylib
    @4
    @20
    @11
    vw
    @20
    @19
    csn
    #
    @8
    wss
    #
    @4
    @11
    @19
    @8
    snssi
    @4
    @5
    @31
    cen
    wbr
    #
    @32
    @31
    @8
    cdom
    wbr
    #
    @11
    @4
    @13
    @19
    cvv
    wcel
    @33
    @16
    vw
    vex
    cA
    @19
    cvv
    cvv
    en2sn
    sylancl
    @4
    cB
    cvv
    wcel
    #
    @8
    cvv
    wcel
    @32
    @34
    wi
    @0
    @35
    @2
    cA
    cB
    csdm
    relsdom
    brrelex2i
    adantr
    cB
    @7
    cvv
    difexg
    @31
    @8
    cvv
    ssdomg
    3syl
    @5
    @31
    @8
    endomtr
    syl6an
    syl5
    exlimdv
    mpd
    @12
    @4
    @7
    cB
    disjdif
    a1i
    cA
    @7
    @5
    @8
    undom
    syl21anc
    @3
    @6
    wceq
    @4
    cA
    df-suc
    a1i
    @4
    @9
    @7
    cB
    cun
    #
    cB
    @7
    cB
    undif2
    @4
    @28
    @36
    cB
    wceq
    @2
    @28
    @0
    @30
    adantl
    @7
    cB
    ssequn1
    sylib
    syl5req
    3brtr4d
    exlimddv
end
