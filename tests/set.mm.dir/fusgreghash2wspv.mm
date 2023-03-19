include "cfusgr.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wi.mm"
include "wa.mm"
include "cnbgr.mm"
include "csn.mm"
include "cdif.mm"
include "cs3.mm"
include "ciun.mm"
include "fusgr2wsp2nb.mm"
include "fveq2d.mm"
include "adantr.mm"
include "cfn.mm"
include "cvtx.mm"
include "eleq2i.mm"
include "nbfiusgrfi.mm"
include "sylan2b.mm"
include "eqid.mm"
include "w3a.mm"
include "snfi.mm"
include "a1i.mm"
include "wdisj.mm"
include "wss.mm"
include "wral.mm"
include "nbgrssvtx.mm"
include "ssdifd.mm"
include "iunss1.mm"
include "syl.mm"
include "ralrimiva.mm"
include "simpr.mm"
include "s3iunsndisj.mm"
include "disjss2.mm"
include "sylc.mm"
include "anim1i.mm"
include "ancomd.mm"
include "s3sndisj.mm"
include "cvv.mm"
include "cword.mm"
include "s3cli.mm"
include "hashsng.mm"
include "mp1i.mm"
include "hash2iun1dif1.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "hashnbusgrvd.mm"
include "sylan.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "sylan9eq.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem fusgreghash2wspv
  let vw: setvar w
  let vv: setvar v
  let cG: class G
  let cK: class K
  let cM: class M
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vc: setvar c
  let vd: setvar d
  assume frgrhash2wsp.v: |- V = ( Vtx ` G )
  assume fusgreg2wsp.m: |- M = ( a e. V |-> { w e. ( 2 WSPathsN G ) | ( w ` 1 ) = a } )

  disjoint G a
  disjoint V a
  disjoint G w
  disjoint a w
  disjoint G v
  disjoint a v
  disjoint v w
  disjoint G b
  disjoint a b
  disjoint V b
  disjoint N a
  disjoint N w
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G p
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint M z
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint V m
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint w z
  disjoint G c
  disjoint G d
  disjoint c d
  disjoint c v
  disjoint d v
  disjoint K c
  disjoint K d
  disjoint V c
  disjoint V d
  assert |- ( G e. FinUSGraph -> A. v e. V ( ( ( VtxDeg ` G ) ` v ) = K -> ( # ` ( M ` v ) ) = ( K x. ( K - 1 ) ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    cfv
    #
    cK
    wceq
    #
    @1
    cM
    cfv
    #
    chash
    cfv
    #
    cK
    cK
    c1
    cmin
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    vv
    cV
    @0
    @1
    cV
    wcel
    #
    wa
    #
    @3
    @8
    @10
    @3
    wa
    #
    @5
    vc
    cG
    @1
    cnbgr
    co
    #
    vd
    @12
    vc
    cv
    #
    csn
    #
    cdif
    #
    @13
    @1
    vd
    cv
    #
    cs3
    #
    csn
    #
    ciun
    #
    ciun
    #
    chash
    cfv
    #
    @12
    chash
    cfv
    #
    @22
    c1
    cmin
    co
    #
    cmul
    co
    #
    @7
    @10
    @5
    @21
    wceq
    @3
    @10
    @4
    @20
    chash
    vc
    vd
    vw
    cG
    cM
    @1
    cV
    va
    frgrhash2wsp.v
    fusgreg2wsp.m
    fusgr2wsp2nb
    fveq2d
    adantr
    @11
    vc
    vd
    @12
    @15
    @18
    @10
    @12
    cfn
    wcel
    #
    @3
    @9
    @0
    @1
    cG
    cvtx
    cfv
    #
    wcel
    @25
    cV
    @26
    @1
    frgrhash2wsp.v
    eleq2i
    cG
    @1
    nbfiusgrfi
    sylan2b
    adantr
    @15
    eqid
    @18
    cfn
    wcel
    @11
    @13
    @12
    wcel
    #
    @16
    @15
    wcel
    w3a
    #
    @17
    snfi
    a1i
    @10
    vc
    @12
    @19
    wdisj
    #
    @3
    @10
    @19
    vd
    cV
    @14
    cdif
    #
    @18
    ciun
    #
    wss
    #
    vc
    @12
    wral
    vc
    @12
    @31
    wdisj
    #
    @29
    @10
    @32
    vc
    @12
    @10
    @27
    wa
    #
    @15
    @30
    wss
    @32
    @34
    @12
    cV
    @14
    @12
    cV
    wss
    @34
    cG
    @1
    cV
    frgrhash2wsp.v
    nbgrssvtx
    a1i
    ssdifd
    vd
    @15
    @30
    @18
    iunss1
    syl
    ralrimiva
    @10
    @9
    @33
    @0
    @9
    simpr
    #
    @1
    cV
    @12
    cV
    vc
    vd
    s3iunsndisj
    syl
    vc
    @12
    @19
    @31
    disjss2
    sylc
    adantr
    @11
    @27
    wa
    #
    @27
    @9
    wa
    vd
    @15
    @18
    wdisj
    @36
    @9
    @27
    @11
    @9
    @27
    @10
    @9
    @3
    @35
    adantr
    anim1i
    ancomd
    @13
    @1
    @12
    cV
    @15
    vd
    s3sndisj
    syl
    @17
    cvv
    cword
    #
    wcel
    @18
    chash
    cfv
    c1
    wceq
    @28
    @13
    @1
    @16
    s3cli
    @17
    @37
    hashsng
    mp1i
    hash2iun1dif1
    @10
    @3
    @24
    @2
    @2
    c1
    cmin
    co
    #
    cmul
    co
    #
    @7
    @10
    @22
    @2
    wceq
    #
    @24
    @39
    wceq
    @0
    cG
    cusgr
    wcel
    @9
    @40
    cG
    fusgrusgr
    @1
    cG
    cV
    frgrhash2wsp.v
    hashnbusgrvd
    sylan
    @40
    @22
    @2
    @23
    @38
    cmul
    @40
    id
    @22
    @2
    c1
    cmin
    oveq1
    oveq12d
    syl
    @3
    @2
    cK
    @38
    @6
    cmul
    @3
    id
    @2
    cK
    c1
    cmin
    oveq1
    oveq12d
    sylan9eq
    3eqtrd
    ex
    ralrimiva
end
