include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cin.mm"
include "cpr.mm"
include "crio.mm"
include "csn.mm"
include "ineq2i.mm"
include "wceq.mm"
include "wrex.mm"
include "cfrgr.mm"
include "wne.mm"
include "w3a.mm"
include "adantr.mm"
include "eleq2i.mm"
include "wi.mm"
include "nbgrisvtx.mm"
include "a1i.mm"
include "syl5bi.mm"
include "imp.mm"
include "wnel.mm"
include "elnelne2.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3jca.mm"
include "frcond3.mm"
include "sylc.mm"
include "cvv.mm"
include "vex.mm"
include "elinsn.mm"
include "mpan.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "nbusgreledg.mm"
include "prcom.mm"
include "eleq1i.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "3syl.mm"
include "com12.mm"
include "wreu.mm"
include "wb.mm"
include "eqcomi.mm"
include "biimpi.mm"
include "adantl.mm"
include "frgrncvvdeqlem2.mm"
include "preq2.mm"
include "eleq1d.mm"
include "riota2.mm"
include "syl2an.mm"
include "mpbid.mm"
include "sylan.mm"
include "eqcomd.mm"
include "sneqd.mm"
include "eqeq1.mm"
include "mpbird.mm"
include "ex.mm"
include "rexlimivw.mm"
include "mpcom.mm"
include "syl5req.mm"

theorem frgrncvvdeqlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vn: setvar n
  assume frgrncvvdeq.v1: |- V = ( Vtx ` G )
  assume frgrncvvdeq.e: |- E = ( Edg ` G )
  assume frgrncvvdeq.nx: |- D = ( G NeighbVtx X )
  assume frgrncvvdeq.ny: |- N = ( G NeighbVtx Y )
  assume frgrncvvdeq.x: |- ( ph -> X e. V )
  assume frgrncvvdeq.y: |- ( ph -> Y e. V )
  assume frgrncvvdeq.ne: |- ( ph -> X =/= Y )
  assume frgrncvvdeq.xy: |- ( ph -> Y e/ D )
  assume frgrncvvdeq.f: |- ( ph -> G e. FriendGraph )
  assume frgrncvvdeq.a: |- A = ( x e. D |-> ( iota_ y e. N { x , y } e. E ) )

  disjoint G y
  disjoint V y
  disjoint Y y
  disjoint x y
  disjoint E y
  disjoint N y
  disjoint D n
  disjoint E n
  disjoint n y
  disjoint G n
  disjoint N n
  disjoint V n
  disjoint Y n
  disjoint n ph
  disjoint n x
  assert |- ( ( ph /\ x e. D ) -> { ( iota_ y e. N { x , y } e. E ) } = ( ( G NeighbVtx x ) i^i N ) )

  proof
    wph
    vx
    cv
    #
    cD
    wcel
    #
    wa
    #
    cG
    @0
    cnbgr
    co
    #
    cN
    cin
    @3
    cG
    cY
    cnbgr
    co
    #
    cin
    #
    @0
    vy
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vy
    cN
    crio
    #
    csn
    #
    cN
    @4
    @3
    frgrncvvdeq.ny
    ineq2i
    @5
    vn
    cv
    #
    csn
    #
    wceq
    #
    vn
    cV
    wrex
    #
    @2
    @5
    @10
    wceq
    #
    @2
    cG
    cfrgr
    wcel
    #
    @0
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @0
    cY
    wne
    #
    w3a
    @14
    wph
    @16
    @1
    frgrncvvdeq.f
    adantr
    @2
    @17
    @18
    @19
    wph
    @1
    @17
    @1
    @0
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    wph
    @17
    cD
    @20
    @0
    frgrncvvdeq.nx
    eleq2i
    @21
    @17
    wi
    wph
    cG
    cX
    @0
    cV
    frgrncvvdeq.v1
    nbgrisvtx
    a1i
    syl5bi
    imp
    wph
    @18
    @1
    frgrncvvdeq.y
    adantr
    @1
    wph
    @19
    wph
    @1
    cY
    cD
    wnel
    @19
    frgrncvvdeq.xy
    @0
    cY
    cD
    elnelne2
    sylan2
    ancoms
    3jca
    vn
    @0
    cY
    cE
    cG
    cV
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frcond3
    sylc
    @13
    @2
    @15
    wi
    vn
    cV
    @13
    @2
    @15
    @13
    @2
    wa
    #
    @15
    @12
    @10
    wceq
    #
    @22
    @11
    @9
    @22
    @9
    @11
    @13
    @11
    @3
    wcel
    #
    @11
    @4
    wcel
    #
    wa
    #
    @2
    @9
    @11
    wceq
    #
    @11
    cvv
    wcel
    @13
    @26
    vn
    vex
    @11
    @3
    @4
    cvv
    elinsn
    mpan
    @26
    @2
    wa
    @0
    @11
    cpr
    #
    cE
    wcel
    #
    @27
    @26
    @2
    @29
    @24
    @2
    @29
    wi
    @25
    @2
    @24
    @29
    wph
    @24
    @29
    wi
    #
    @1
    wph
    @16
    cG
    cusgr
    wcel
    #
    @30
    frgrncvvdeq.f
    cG
    frgrusgr
    @31
    @24
    @29
    @31
    @24
    @11
    @0
    cpr
    #
    cE
    wcel
    @29
    cE
    cG
    @0
    @11
    frgrncvvdeq.e
    nbusgreledg
    @32
    @28
    cE
    @11
    @0
    prcom
    eleq1i
    syl6bb
    biimpd
    3syl
    adantr
    com12
    adantr
    imp
    @26
    @11
    cN
    wcel
    #
    @8
    vy
    cN
    wreu
    @29
    @27
    wb
    @2
    @25
    @33
    @24
    @25
    @33
    @4
    cN
    @11
    cN
    @4
    frgrncvvdeq.ny
    eqcomi
    eleq2i
    biimpi
    adantl
    wph
    vx
    vy
    cA
    cD
    cE
    cG
    cN
    cV
    cX
    cY
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrncvvdeq.ny
    frgrncvvdeq.x
    frgrncvvdeq.y
    frgrncvvdeq.ne
    frgrncvvdeq.xy
    frgrncvvdeq.f
    frgrncvvdeq.a
    frgrncvvdeqlem2
    @8
    @29
    vy
    cN
    @11
    @6
    @11
    wceq
    @7
    @28
    cE
    @6
    @11
    @0
    preq2
    eleq1d
    riota2
    syl2an
    mpbid
    sylan
    eqcomd
    sneqd
    @13
    @15
    @23
    wb
    @2
    @5
    @12
    @10
    eqeq1
    adantr
    mpbird
    ex
    rexlimivw
    mpcom
    syl5req
end
