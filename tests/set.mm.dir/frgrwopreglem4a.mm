include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "wceq.mm"
include "wi.mm"
include "fveq2.mm"
include "a1i.mm"
include "necon3d.mm"
include "imp.mm"
include "3adant1.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "frgrncvvdeq.mm"
include "wb.mm"
include "oveq2.mm"
include "neleq2.mm"
include "syl.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "neleq1.mm"
include "eqeq2d.mm"
include "simpll.mm"
include "sneq.mm"
include "difeq2d.mm"
include "adantl.mm"
include "simpr.mm"
include "necom.mm"
include "biimpi.mm"
include "anim12i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "rspc2vd.mm"
include "wn.mm"
include "nnel.mm"
include "nbgrsym.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "nbusgreledg.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "a1d.mm"
include "expcom.mm"
include "sylbi.mm"
include "eqneqall.mm"
include "2a1d.mm"
include "ja.mm"
include "com12.mm"
include "syld.mm"
include "com3l.mm"
include "mpcom.mm"
include "expd.mm"
include "com34.mm"
include "3imp.mm"
include "mpd.mm"

theorem frgrwopreglem4a
  let cD: class D
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume frgrncvvdeq.v: |- V = ( Vtx ` G )
  assume frgrncvvdeq.d: |- D = ( VtxDeg ` G )
  assume frgrwopreglem4a.e: |- E = ( Edg ` G )


  assert |- ( ( G e. FriendGraph /\ ( X e. V /\ Y e. V ) /\ ( D ` X ) =/= ( D ` Y ) ) -> { X , Y } e. E )

  proof
    cG
    cfrgr
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cD
    cfv
    #
    cY
    cD
    cfv
    #
    wne
    #
    w3a
    cX
    cY
    wne
    #
    cX
    cY
    cpr
    cE
    wcel
    #
    @3
    @6
    @7
    @0
    @3
    @6
    @7
    @3
    cX
    cY
    @4
    @5
    cX
    cY
    wceq
    @4
    @5
    wceq
    #
    wi
    @3
    cX
    cY
    cD
    fveq2
    a1i
    necon3d
    imp
    3adant1
    @0
    @3
    @6
    @7
    @8
    wi
    @0
    @3
    @7
    @6
    @8
    @0
    @3
    @7
    @6
    @8
    wi
    #
    vy
    cv
    #
    cG
    vx
    cv
    #
    cnbgr
    co
    #
    wnel
    #
    @12
    cD
    cfv
    #
    @11
    cD
    cfv
    #
    wceq
    #
    wi
    #
    vy
    cV
    @12
    csn
    #
    cdif
    #
    wral
    vx
    cV
    wral
    #
    @0
    @3
    @7
    wa
    #
    @10
    wi
    vx
    vy
    cD
    cG
    cV
    frgrncvvdeq.v
    frgrncvvdeq.d
    frgrncvvdeq
    @22
    @21
    @0
    @10
    @22
    @21
    cY
    cG
    cX
    cnbgr
    co
    #
    wnel
    #
    @9
    wi
    #
    @0
    @10
    wi
    #
    @22
    @25
    @11
    @23
    wnel
    #
    @4
    @16
    wceq
    #
    wi
    @18
    vx
    vy
    cX
    cY
    cV
    @20
    cV
    cX
    csn
    #
    cdif
    #
    @12
    cX
    wceq
    #
    @14
    @27
    @17
    @28
    @31
    @13
    @23
    wceq
    @14
    @27
    wb
    @12
    cX
    cG
    cnbgr
    oveq2
    @13
    @23
    @11
    neleq2
    syl
    @31
    @15
    @4
    @16
    @12
    cX
    cD
    fveq2
    eqeq1d
    imbi12d
    @11
    cY
    wceq
    #
    @27
    @24
    @28
    @9
    @11
    cY
    @23
    neleq1
    @32
    @16
    @5
    @4
    @11
    cY
    cD
    fveq2
    eqeq2d
    imbi12d
    @1
    @2
    @7
    simpll
    @31
    @20
    @30
    wceq
    @22
    @31
    @19
    @29
    cV
    @12
    cX
    sneq
    difeq2d
    adantl
    @22
    @2
    cY
    cX
    wne
    #
    wa
    cY
    @30
    wcel
    @3
    @2
    @7
    @33
    @1
    @2
    simpr
    @7
    @33
    cX
    cY
    necom
    biimpi
    anim12i
    cY
    cV
    cX
    eldifsn
    sylibr
    rspc2vd
    @25
    @22
    @26
    @24
    @9
    @22
    @26
    wi
    #
    @24
    wn
    cY
    @23
    wcel
    #
    @34
    cY
    @23
    nnel
    @35
    @26
    @22
    @0
    @35
    @10
    @0
    @35
    wa
    @8
    @6
    @0
    @35
    @8
    @35
    cX
    cG
    cY
    cnbgr
    co
    wcel
    #
    @0
    @8
    cG
    cX
    cY
    nbgrsym
    @0
    @36
    @8
    @0
    cG
    cusgr
    wcel
    @36
    @8
    wb
    cG
    frgrusgr
    cE
    cG
    cY
    cX
    frgrwopreglem4a.e
    nbusgreledg
    syl
    biimpd
    syl5bi
    imp
    a1d
    expcom
    a1d
    sylbi
    @9
    @10
    @22
    @0
    @8
    @4
    @5
    eqneqall
    2a1d
    ja
    com12
    syld
    com3l
    mpcom
    expd
    com34
    3imp
    mpd
end
