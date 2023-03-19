include "cupgr.mm"
include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "upgrn0.mm"
include "n0.mm"
include "sylib.mm"
include "cdm.mm"
include "wss.mm"
include "simp1.mm"
include "wi.mm"
include "fndm.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "a1i.mm"
include "3imp.mm"
include "upgrss.mm"
include "syl2anc.mm"
include "sselda.mm"
include "csn.mm"
include "cdif.mm"
include "adantr.mm"
include "simpr.mm"
include "ssdif0.mm"
include "sylibr.mm"
include "snssd.mm"
include "eqssd.mm"
include "preq2.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "simprr.mm"
include "eldifad.mm"
include "sseldd.mm"
include "cfn.mm"
include "cen.mm"
include "wbr.mm"
include "upgrfi.mm"
include "simprl.mm"
include "prssd.mm"
include "cdom.mm"
include "cvv.mm"
include "fvex.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "chash.mm"
include "cle.mm"
include "c2.mm"
include "upgrle.mm"
include "eldifsni.mm"
include "ad2antll.mm"
include "necomd.mm"
include "wb.mm"
include "vex.mm"
include "hashprg.mm"
include "mp2an.mm"
include "breqtrrd.mm"
include "prfi.mm"
include "hashdom.mm"
include "sylancl.mm"
include "mpbid.mm"
include "sbth.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "jca.mm"
include "expr.mm"
include "eximdv.mm"
include "imp.mm"
include "df-rex.mm"
include "sylan2b.mm"
include "pm2.61dane.mm"
include "ex.mm"
include "mpd.mm"

theorem upgrex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isupgr.v: |- V = ( Vtx ` G )
  assume isupgr.e: |- E = ( iEdg ` G )

  disjoint G x
  disjoint V x
  disjoint E x
  disjoint F x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint E y
  disjoint F y
  disjoint G y
  disjoint V y
  disjoint e g
  disjoint e h
  disjoint e v
  disjoint e x
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint h v
  disjoint h x
  disjoint v x
  disjoint E h
  disjoint G h
  disjoint V h
  assert |- ( ( G e. UPGraph /\ E Fn A /\ F e. A ) -> E. x e. V E. y e. V ( E ` F ) = { x , y } )

  proof
    cG
    cupgr
    wcel
    #
    cE
    cA
    wfn
    #
    cF
    cA
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cV
    wcel
    #
    cF
    cE
    cfv
    #
    @4
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vy
    cV
    wrex
    #
    wa
    #
    vx
    wex
    #
    @10
    vx
    cV
    wrex
    @3
    @4
    @6
    wcel
    #
    vx
    wex
    #
    @12
    @3
    @6
    c0
    wne
    @14
    cA
    cE
    cF
    cG
    cV
    isupgr.v
    isupgr.e
    upgrn0
    vx
    @6
    n0
    sylib
    @3
    @13
    @11
    vx
    @3
    @13
    @11
    @3
    @13
    wa
    #
    @5
    @10
    @3
    @6
    cV
    @4
    @3
    @0
    cF
    cE
    cdm
    #
    wcel
    #
    @6
    cV
    wss
    #
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    @17
    @1
    @2
    @17
    wi
    wi
    @0
    @1
    @2
    @17
    @1
    cA
    @16
    cF
    @1
    @16
    cA
    cA
    cE
    fndm
    eqcomd
    eleq2d
    biimpd
    a1i
    3imp
    cE
    cF
    cG
    cV
    isupgr.v
    isupgr.e
    upgrss
    syl2anc
    #
    sselda
    #
    @15
    @10
    @6
    @4
    csn
    #
    cdif
    #
    c0
    @15
    @22
    c0
    wceq
    #
    wa
    #
    @5
    @6
    @21
    wceq
    #
    @10
    @15
    @5
    @23
    @20
    adantr
    @24
    @6
    @21
    @24
    @23
    @6
    @21
    wss
    @15
    @23
    simpr
    @6
    @21
    ssdif0
    sylibr
    @15
    @21
    @6
    wss
    @23
    @15
    @4
    @6
    @3
    @13
    simpr
    snssd
    adantr
    eqssd
    @9
    @25
    vy
    @4
    cV
    @7
    @4
    wceq
    #
    @8
    @21
    @6
    @26
    @8
    @4
    @4
    cpr
    @21
    @7
    @4
    @4
    preq2
    @4
    dfsn2
    syl6eqr
    eqeq2d
    rspcev
    syl2anc
    @22
    c0
    wne
    @15
    @7
    @22
    wcel
    #
    vy
    wex
    #
    @10
    vy
    @22
    n0
    @15
    @28
    wa
    @7
    cV
    wcel
    #
    @9
    wa
    #
    vy
    wex
    #
    @10
    @15
    @28
    @31
    @15
    @27
    @30
    vy
    @3
    @13
    @27
    @30
    @3
    @13
    @27
    wa
    #
    wa
    #
    @29
    @9
    @33
    @6
    cV
    @7
    @3
    @18
    @32
    @19
    adantr
    @33
    @7
    @6
    @21
    @3
    @13
    @27
    simprr
    eldifad
    #
    sseldd
    @33
    @8
    @6
    @33
    @6
    cfn
    wcel
    #
    @8
    @6
    wss
    #
    @8
    @6
    cen
    wbr
    #
    @8
    @6
    wceq
    @3
    @35
    @32
    cA
    cE
    cF
    cG
    cV
    isupgr.v
    isupgr.e
    upgrfi
    adantr
    #
    @33
    @4
    @7
    @6
    @3
    @13
    @27
    simprl
    @34
    prssd
    #
    @33
    @8
    @6
    cdom
    wbr
    #
    @6
    @8
    cdom
    wbr
    #
    @37
    @6
    cvv
    wcel
    @33
    @36
    @40
    cF
    cE
    fvex
    @39
    @8
    @6
    cvv
    ssdomg
    mpsyl
    @33
    @6
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    cle
    wbr
    #
    @41
    @33
    @42
    c2
    @43
    cle
    @3
    @42
    c2
    cle
    wbr
    @32
    cA
    cE
    cF
    cG
    cV
    isupgr.v
    isupgr.e
    upgrle
    adantr
    @33
    @4
    @7
    wne
    #
    @43
    c2
    wceq
    #
    @33
    @7
    @4
    @27
    @7
    @4
    wne
    @3
    @13
    @7
    @6
    @4
    eldifsni
    ad2antll
    necomd
    @4
    cvv
    wcel
    @7
    cvv
    wcel
    @45
    @46
    wb
    vx
    vex
    vy
    vex
    @4
    @7
    cvv
    cvv
    hashprg
    mp2an
    sylib
    breqtrrd
    @33
    @35
    @8
    cfn
    wcel
    @44
    @41
    wb
    @38
    @4
    @7
    prfi
    @6
    @8
    cfn
    hashdom
    sylancl
    mpbid
    @8
    @6
    sbth
    syl2anc
    @8
    @6
    fisseneq
    syl3anc
    eqcomd
    jca
    expr
    eximdv
    imp
    @9
    vy
    cV
    df-rex
    sylibr
    sylan2b
    pm2.61dane
    jca
    ex
    eximdv
    mpd
    @10
    vx
    cV
    df-rex
    sylibr
end
