include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cvtxdg.mm"
include "chash.mm"
include "cvv.mm"
include "cpr.mm"
include "cedg.mm"
include "crio.mm"
include "cmpt.mm"
include "ovexd.mm"
include "eqid.mm"
include "simpl.mm"
include "ad2antlr.mm"
include "eldifi.mm"
include "adantl.mm"
include "wne.mm"
include "wn.mm"
include "eldif.mm"
include "velsn.mm"
include "biimpri.mm"
include "equcoms.mm"
include "necon3bi.mm"
include "simplbiim.mm"
include "simpr.mm"
include "adantr.mm"
include "frgrncvvdeqlem10.mm"
include "hasheqf1od.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "anim12i.mm"
include "hashnbusgrvd.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "fveq1i.mm"
include "3eqtr4g.mm"
include "ex.mm"
include "ralrimivva.mm"

theorem frgrncvvdeq
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume frgrncvvdeq.v: |- V = ( Vtx ` G )
  assume frgrncvvdeq.d: |- D = ( VtxDeg ` G )

  disjoint G x
  disjoint G y
  disjoint x y
  disjoint V x
  disjoint V y
  disjoint G a
  disjoint G b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint V a
  disjoint V b
  assert |- ( G e. FriendGraph -> A. x e. V A. y e. ( V \ { x } ) ( y e/ ( G NeighbVtx x ) -> ( D ` x ) = ( D ` y ) ) )

  proof
    cG
    cfrgr
    wcel
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
    @2
    cD
    cfv
    #
    @1
    cD
    cfv
    #
    wceq
    #
    wi
    vx
    vy
    cV
    cV
    @2
    csn
    #
    cdif
    #
    @0
    @2
    cV
    wcel
    #
    @1
    @9
    wcel
    #
    wa
    #
    wa
    #
    @4
    @7
    @13
    @4
    wa
    #
    @2
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    @1
    @15
    cfv
    #
    @5
    @6
    @14
    @3
    chash
    cfv
    #
    cG
    @1
    cnbgr
    co
    #
    chash
    cfv
    #
    @16
    @17
    @14
    @3
    @19
    cvv
    va
    @3
    va
    cv
    vb
    cv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vb
    @19
    crio
    cmpt
    #
    @14
    cG
    @2
    cnbgr
    ovexd
    @14
    va
    vb
    @22
    @3
    @21
    cG
    @19
    cV
    @2
    @1
    frgrncvvdeq.v
    @21
    eqid
    @3
    eqid
    @19
    eqid
    @12
    @10
    @0
    @4
    @10
    @11
    simpl
    #
    ad2antlr
    @12
    @1
    cV
    wcel
    #
    @0
    @4
    @11
    @24
    @10
    @1
    cV
    @8
    eldifi
    adantl
    #
    ad2antlr
    @12
    @2
    @1
    wne
    #
    @0
    @4
    @11
    @26
    @10
    @11
    @24
    @1
    @8
    wcel
    #
    wn
    @26
    @1
    cV
    @8
    eldif
    @27
    @2
    @1
    @27
    vy
    vx
    @27
    @1
    @2
    wceq
    vy
    @2
    velsn
    biimpri
    equcoms
    necon3bi
    simplbiim
    adantl
    ad2antlr
    @13
    @4
    simpr
    @13
    @0
    @4
    @0
    @12
    simpl
    adantr
    @22
    eqid
    frgrncvvdeqlem10
    hasheqf1od
    @14
    cG
    cusgr
    wcel
    #
    @10
    wa
    #
    @18
    @16
    wceq
    @13
    @29
    @4
    @0
    @28
    @12
    @10
    cG
    frgrusgr
    #
    @23
    anim12i
    adantr
    @2
    cG
    cV
    frgrncvvdeq.v
    hashnbusgrvd
    syl
    @14
    @28
    @24
    wa
    #
    @20
    @17
    wceq
    @13
    @31
    @4
    @0
    @28
    @12
    @24
    @30
    @25
    anim12i
    adantr
    @1
    cG
    cV
    frgrncvvdeq.v
    hashnbusgrvd
    syl
    3eqtr3d
    @2
    cD
    @15
    frgrncvvdeq.d
    fveq1i
    @1
    cD
    @15
    frgrncvvdeq.d
    fveq1i
    3eqtr4g
    ex
    ralrimivva
end
