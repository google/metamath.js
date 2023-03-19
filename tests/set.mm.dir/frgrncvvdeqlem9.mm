include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "frgrncvvdeqlem4.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cpr.mm"
include "cfrgr.mm"
include "wne.mm"
include "w3a.mm"
include "wreu.mm"
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
include "frgrncvvdeqlem1.mm"
include "wn.mm"
include "df-nel.mm"
include "nelelne.mm"
include "sylbi.mm"
include "syl.mm"
include "3jca.mm"
include "jca.mm"
include "frcond2.mm"
include "reurex.mm"
include "df-rex.mm"
include "sylib.mm"
include "3syl.mm"
include "cusgr.mm"
include "wb.mm"
include "frgrusgr.mm"
include "nbusgreledg.mm"
include "bicomd.mm"
include "biimpa.mm"
include "sylibr.mm"
include "ad2ant2rl.mm"
include "biimpar.mm"
include "a1d.mm"
include "expimpd.mm"
include "cin.mm"
include "elin.mm"
include "csn.mm"
include "simpl.mm"
include "crio.mm"
include "cmpt.mm"
include "preq1.mm"
include "eleq1d.mm"
include "riotabidv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "frgrncvvdeqlem5.mm"
include "eleq2.mm"
include "eqcoms.mm"
include "elsni.mm"
include "syl6bi.mm"
include "expcom.mm"
include "com3r.mm"
include "sylbir.mm"
include "ex.mm"
include "com14.mm"
include "adantld.mm"
include "mpd.mm"
include "eximdv.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem frgrncvvdeqlem9
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
  let vu: setvar u
  let vw: setvar w
  let vm: setvar m
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
  disjoint D x
  disjoint N x
  disjoint ph x
  disjoint D y
  disjoint E x
  disjoint D n
  disjoint E n
  disjoint n y
  disjoint G n
  disjoint N n
  disjoint V n
  disjoint Y n
  disjoint n ph
  disjoint n x
  disjoint A u
  disjoint A w
  disjoint u w
  disjoint D u
  disjoint D w
  disjoint u y
  disjoint w y
  disjoint E u
  disjoint E w
  disjoint u x
  disjoint w x
  disjoint N u
  disjoint N w
  disjoint ph u
  disjoint ph w
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint D m
  disjoint m x
  disjoint E m
  disjoint G m
  disjoint m y
  disjoint N m
  disjoint V m
  disjoint X m
  disjoint X n
  disjoint m ph
  assert |- ( ph -> A : D -onto-> N )

  proof
    wph
    cD
    cN
    cA
    wf
    vn
    cv
    #
    vm
    cv
    #
    cA
    cfv
    #
    wceq
    #
    vm
    cD
    wrex
    #
    vn
    cN
    wral
    cD
    cN
    cA
    wfo
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
    frgrncvvdeqlem4
    wph
    @4
    vn
    cN
    wph
    @0
    cN
    wcel
    #
    wa
    #
    @1
    cD
    wcel
    #
    @3
    wa
    #
    vm
    wex
    #
    @4
    @6
    @1
    cV
    wcel
    #
    @0
    @1
    cpr
    cE
    wcel
    #
    @1
    cX
    cpr
    cE
    wcel
    #
    wa
    #
    wa
    #
    vm
    wex
    #
    @9
    @6
    cG
    cfrgr
    wcel
    #
    @0
    cV
    wcel
    #
    cX
    cV
    wcel
    #
    @0
    cX
    wne
    #
    w3a
    #
    wa
    @13
    vm
    cV
    wreu
    #
    @15
    @6
    @16
    @20
    wph
    @16
    @5
    frgrncvvdeq.f
    adantr
    @6
    @17
    @18
    @19
    wph
    @5
    @17
    @5
    @0
    cG
    cY
    cnbgr
    co
    #
    wcel
    #
    wph
    @17
    cN
    @22
    @0
    frgrncvvdeq.ny
    eleq2i
    @23
    @17
    wi
    wph
    cG
    cY
    @0
    cV
    frgrncvvdeq.v1
    nbgrisvtx
    a1i
    syl5bi
    imp
    wph
    @18
    @5
    frgrncvvdeq.x
    adantr
    wph
    @5
    @19
    wph
    cX
    cN
    wnel
    #
    @5
    @19
    wi
    #
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
    frgrncvvdeqlem1
    @24
    cX
    cN
    wcel
    wn
    @25
    cX
    cN
    df-nel
    cX
    cN
    @0
    nelelne
    sylbi
    syl
    imp
    3jca
    jca
    @16
    @20
    @21
    @0
    cX
    cE
    cG
    cV
    vm
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frcond2
    imp
    @21
    @13
    vm
    cV
    wrex
    @15
    @13
    vm
    cV
    reurex
    @13
    vm
    cV
    df-rex
    sylib
    3syl
    @6
    @14
    @8
    vm
    @6
    @13
    @8
    @10
    @6
    @13
    @8
    @6
    @13
    wa
    #
    @7
    @3
    wph
    @12
    @7
    @5
    @11
    wph
    @12
    wa
    #
    @1
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    @7
    wph
    @12
    @29
    wph
    @16
    cG
    cusgr
    wcel
    #
    @12
    @29
    wb
    frgrncvvdeq.f
    cG
    frgrusgr
    #
    @30
    @29
    @12
    cE
    cG
    cX
    @1
    frgrncvvdeq.e
    nbusgreledg
    bicomd
    3syl
    biimpa
    cD
    @28
    @1
    frgrncvvdeq.nx
    eleq2i
    sylibr
    #
    ad2ant2rl
    @26
    @0
    cG
    @1
    cnbgr
    co
    #
    wcel
    #
    @3
    @6
    @13
    @34
    wph
    @13
    @34
    wi
    #
    @5
    wph
    @16
    @30
    @35
    frgrncvvdeq.f
    @31
    @30
    @11
    @12
    @34
    @30
    @11
    wa
    @34
    @12
    @30
    @34
    @11
    cE
    cG
    @1
    @0
    frgrncvvdeq.e
    nbusgreledg
    biimpar
    a1d
    expimpd
    3syl
    adantr
    imp
    @6
    @13
    @34
    @3
    wi
    #
    @6
    @12
    @36
    @11
    wph
    @5
    @12
    @36
    wi
    @34
    @5
    @12
    wph
    @3
    @34
    @5
    @12
    wph
    @3
    wi
    wi
    #
    @34
    @5
    wa
    @0
    @33
    cN
    cin
    #
    wcel
    #
    @37
    @0
    @33
    cN
    elin
    @12
    wph
    @39
    @3
    wph
    @12
    @39
    @3
    wi
    #
    @27
    wph
    @7
    wa
    @2
    csn
    #
    @38
    wceq
    #
    @40
    @27
    wph
    @7
    wph
    @12
    simpl
    @32
    jca
    wph
    vm
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
    cA
    vx
    cD
    vx
    cv
    #
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
    cmpt
    vm
    cD
    @1
    @44
    cpr
    #
    cE
    wcel
    #
    vy
    cN
    crio
    #
    cmpt
    frgrncvvdeq.a
    vx
    vm
    cD
    @47
    @50
    @43
    @1
    wceq
    #
    @46
    @49
    vy
    cN
    @51
    @45
    @48
    cE
    @43
    @1
    @44
    preq1
    eleq1d
    riotabidv
    cbvmptv
    eqtri
    frgrncvvdeqlem5
    @42
    @39
    @0
    @41
    wcel
    #
    @3
    @39
    @52
    wb
    @38
    @41
    @38
    @41
    @0
    eleq2
    eqcoms
    @0
    @2
    elsni
    syl6bi
    3syl
    expcom
    com3r
    sylbir
    ex
    com14
    imp
    adantld
    imp
    mpd
    jca
    ex
    adantld
    eximdv
    mpd
    @3
    vm
    cD
    df-rex
    sylibr
    ralrimiva
    vm
    vn
    cD
    cN
    cA
    dffo3
    sylanbrc
end
