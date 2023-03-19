include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "cfrgr.mm"
include "wne.mm"
include "w3a.mm"
include "adantr.mm"
include "cnbgr.mm"
include "co.mm"
include "eleq2i.mm"
include "wi.mm"
include "nbgrisvtx.mm"
include "a1i.mm"
include "syl5bi.mm"
include "imp.mm"
include "wnel.mm"
include "elnelne2.mm"
include "expcom.mm"
include "syl.mm"
include "3jca.mm"
include "frcond1.mm"
include "sylc.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "weu.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "umgrpredgv.mm"
include "simprd.mm"
include "ex.mm"
include "adantld.mm"
include "pm4.71rd.mm"
include "prex.mm"
include "prss.mm"
include "ancom.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "syl6rbbr.mm"
include "nbusgreledg.mm"
include "syl5rbb.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "eubidv.mm"
include "biimpd.mm"
include "df-reu.mm"
include "3imtr4g.mm"
include "3syl.mm"
include "mpd.mm"

theorem frgrncvvdeqlem2
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
  assert |- ( ( ph /\ x e. D ) -> E! y e. N { x , y } e. E )

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
    @0
    vy
    cv
    #
    cpr
    #
    @3
    cY
    cpr
    #
    cpr
    cE
    wss
    #
    vy
    cV
    wreu
    #
    @4
    cE
    wcel
    #
    vy
    cN
    wreu
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
    @7
    wph
    @10
    @1
    frgrncvvdeq.f
    adantr
    @2
    @11
    @12
    @13
    wph
    @1
    @11
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
    @11
    cD
    @14
    @0
    frgrncvvdeq.nx
    eleq2i
    @15
    @11
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
    @12
    @1
    frgrncvvdeq.y
    adantr
    wph
    @1
    @13
    wph
    cY
    cD
    wnel
    #
    @1
    @13
    wi
    frgrncvvdeq.xy
    @1
    @16
    @13
    @0
    cY
    cD
    elnelne2
    expcom
    syl
    imp
    3jca
    @0
    cY
    cE
    cG
    cV
    vy
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frcond1
    sylc
    wph
    @7
    @9
    wi
    #
    @1
    wph
    @10
    cG
    cusgr
    wcel
    #
    @17
    frgrncvvdeq.f
    cG
    frgrusgr
    @18
    @3
    cV
    wcel
    #
    @6
    wa
    #
    vy
    weu
    #
    @3
    cN
    wcel
    #
    @8
    wa
    #
    vy
    weu
    #
    @7
    @9
    @18
    @21
    @24
    @18
    @20
    @23
    vy
    @18
    @20
    @5
    cE
    wcel
    #
    @8
    wa
    #
    @23
    @18
    @26
    @19
    @26
    wa
    @20
    @18
    @26
    @19
    @18
    @8
    @19
    @25
    @18
    cG
    cumgr
    wcel
    #
    @8
    @19
    wi
    cG
    usgrumgr
    @27
    @8
    @19
    @27
    @8
    wa
    @11
    @19
    cE
    cG
    @0
    @3
    cV
    frgrncvvdeq.v1
    frgrncvvdeq.e
    umgrpredgv
    simprd
    ex
    syl
    adantld
    pm4.71rd
    @6
    @26
    @19
    @6
    @8
    @25
    wa
    @26
    @4
    @5
    cE
    @0
    @3
    prex
    @3
    cY
    prex
    prss
    @8
    @25
    ancom
    bitr3i
    anbi2i
    syl6rbbr
    @18
    @25
    @22
    @8
    @22
    @3
    cG
    cY
    cnbgr
    co
    #
    wcel
    @18
    @25
    cN
    @28
    @3
    frgrncvvdeq.ny
    eleq2i
    cE
    cG
    cY
    @3
    frgrncvvdeq.e
    nbusgreledg
    syl5rbb
    anbi1d
    bitrd
    eubidv
    biimpd
    @6
    vy
    cV
    df-reu
    @8
    vy
    cN
    df-reu
    3imtr4g
    3syl
    adantr
    mpd
end
