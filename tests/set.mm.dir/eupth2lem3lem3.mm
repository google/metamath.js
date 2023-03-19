include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cc0.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "wcel.mm"
include "wb.mm"
include "cv.mm"
include "crab.mm"
include "fveq2.mm"
include "breq2d.mm"
include "notbid.mm"
include "elrab3.mm"
include "syl.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "adantr.mm"
include "cz.mm"
include "2z.mm"
include "a1i.mm"
include "eupth2lem3lem1.mm"
include "nn0zd.mm"
include "eupth2lem3lem2.mm"
include "iddvds.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cvtx.mm"
include "ad2antrr.mm"
include "fvexd.mm"
include "ciedg.mm"
include "cop.mm"
include "csn.mm"
include "wss.mm"
include "wif.mm"
include "ifptru.mm"
include "adantl.mm"
include "mpbid.mm"
include "sneq.mm"
include "eqcoms.mm"
include "sylan9eq.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "1loopgrvd2.mm"
include "syl5breqr.mm"
include "wne.mm"
include "dvds0.mm"
include "trlsegvdeglem1.mm"
include "simpld.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "1loopgrvd0.mm"
include "pm2.61dane.mm"
include "dvdsadd2b.mm"
include "syl112anc.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "bitrd.mm"
include "simpr.mm"
include "eqeq2d.mm"
include "preq2d.mm"
include "ifbieq2d.mm"
include "3bitr3d.mm"

theorem eupth2lem3lem3
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume trlsegvdeg.v: |- V = ( Vtx ` G )
  assume trlsegvdeg.i: |- I = ( iEdg ` G )
  assume trlsegvdeg.f: |- ( ph -> Fun I )
  assume trlsegvdeg.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume trlsegvdeg.u: |- ( ph -> U e. V )
  assume trlsegvdeg.w: |- ( ph -> F ( Trails ` G ) P )
  assume trlsegvdeg.vx: |- ( ph -> ( Vtx ` X ) = V )
  assume trlsegvdeg.vy: |- ( ph -> ( Vtx ` Y ) = V )
  assume trlsegvdeg.vz: |- ( ph -> ( Vtx ` Z ) = V )
  assume trlsegvdeg.ix: |- ( ph -> ( iEdg ` X ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume trlsegvdeg.iy: |- ( ph -> ( iEdg ` Y ) = { <. ( F ` N ) , ( I ` ( F ` N ) ) >. } )
  assume trlsegvdeg.iz: |- ( ph -> ( iEdg ` Z ) = ( I |` ( F " ( 0 ... N ) ) ) )
  assume eupth2lem3.o: |- ( ph -> { x e. V | -. 2 || ( ( VtxDeg ` X ) ` x ) } = if ( ( P ` 0 ) = ( P ` N ) , (/) , { ( P ` 0 ) , ( P ` N ) } ) )
  assume eupth2lem3lem3.e: |- ( ph -> if- ( ( P ` N ) = ( P ` ( N + 1 ) ) , ( I ` ( F ` N ) ) = { ( P ` N ) } , { ( P ` N ) , ( P ` ( N + 1 ) ) } C_ ( I ` ( F ` N ) ) ) )

  disjoint U x
  disjoint V x
  disjoint X x
  assert |- ( ( ph /\ ( P ` N ) = ( P ` ( N + 1 ) ) ) -> ( -. 2 || ( ( ( VtxDeg ` X ) ` U ) + ( ( VtxDeg ` Y ) ` U ) ) <-> U e. if ( ( P ` 0 ) = ( P ` ( N + 1 ) ) , (/) , { ( P ` 0 ) , ( P ` ( N + 1 ) ) } ) ) )

  proof
    wph
    cN
    cP
    cfv
    #
    cN
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    #
    wa
    #
    c2
    cU
    cX
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    cU
    cc0
    cP
    cfv
    #
    @0
    wceq
    #
    c0
    @8
    @0
    cpr
    #
    cif
    #
    wcel
    #
    c2
    @5
    cU
    cY
    cvtxdg
    cfv
    cfv
    #
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    cU
    @8
    @1
    wceq
    #
    c0
    @8
    @1
    cpr
    #
    cif
    #
    wcel
    wph
    @7
    @12
    wb
    @2
    wph
    cU
    c2
    vx
    cv
    #
    @4
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    wcel
    #
    @7
    @12
    wph
    cU
    cV
    wcel
    #
    @24
    @7
    wb
    trlsegvdeg.u
    @22
    @7
    vx
    cU
    cV
    @19
    cU
    wceq
    #
    @21
    @6
    @26
    @20
    @5
    c2
    cdvds
    @19
    cU
    @4
    fveq2
    breq2d
    notbid
    elrab3
    syl
    wph
    @23
    @11
    cU
    eupth2lem3.o
    eleq2d
    bitr3d
    adantr
    @3
    @6
    @15
    @3
    @6
    c2
    @13
    @5
    caddc
    co
    #
    cdvds
    wbr
    #
    @15
    @3
    c2
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    c2
    @13
    cdvds
    wbr
    #
    @6
    @28
    wb
    @29
    @3
    2z
    a1i
    wph
    @30
    @2
    wph
    @5
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    eupth2lem3lem1
    #
    nn0zd
    adantr
    wph
    @31
    @2
    wph
    @13
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    eupth2lem3lem2
    #
    nn0zd
    adantr
    @3
    @32
    cU
    @0
    @3
    cU
    @0
    wceq
    #
    wa
    #
    c2
    c2
    @13
    cdvds
    @29
    c2
    c2
    cdvds
    wbr
    2z
    c2
    iddvds
    ax-mp
    @36
    cN
    cF
    cfv
    #
    cY
    cU
    cV
    cvv
    wph
    cY
    cvtx
    cfv
    cV
    wceq
    #
    @2
    @35
    trlsegvdeg.vy
    ad2antrr
    @36
    cN
    cF
    fvexd
    wph
    @25
    @2
    @35
    trlsegvdeg.u
    ad2antrr
    @36
    cY
    ciedg
    cfv
    #
    @37
    @37
    cI
    cfv
    #
    cop
    #
    csn
    #
    @37
    cU
    csn
    #
    cop
    #
    csn
    wph
    @39
    @42
    wceq
    #
    @2
    @35
    trlsegvdeg.iy
    ad2antrr
    @36
    @41
    @44
    @36
    @40
    @43
    @37
    @3
    @35
    @40
    @0
    csn
    #
    @43
    @3
    @2
    @40
    @46
    wceq
    #
    @0
    @1
    cpr
    @40
    wss
    #
    wif
    #
    @47
    wph
    @49
    @2
    eupth2lem3lem3.e
    adantr
    @2
    @49
    @47
    wb
    wph
    @2
    @47
    @48
    ifptru
    adantl
    mpbid
    #
    @46
    @43
    wceq
    @0
    cU
    @0
    cU
    sneq
    eqcoms
    sylan9eq
    opeq2d
    sneqd
    eqtrd
    1loopgrvd2
    syl5breqr
    @3
    cU
    @0
    wne
    #
    wa
    #
    c2
    cc0
    @13
    cdvds
    @29
    c2
    cc0
    cdvds
    wbr
    2z
    c2
    dvds0
    ax-mp
    @52
    @37
    cY
    cU
    @0
    cV
    cvv
    wph
    @38
    @2
    @51
    trlsegvdeg.vy
    ad2antrr
    @52
    cN
    cF
    fvexd
    wph
    @0
    cV
    wcel
    #
    @2
    @51
    wph
    @53
    @1
    cV
    wcel
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeglem1
    simpld
    ad2antrr
    @3
    @39
    @37
    @46
    cop
    #
    csn
    #
    wceq
    @51
    @3
    @39
    @42
    @55
    wph
    @45
    @2
    trlsegvdeg.iy
    adantr
    @3
    @41
    @54
    @3
    @40
    @46
    @37
    @50
    opeq2d
    sneqd
    eqtrd
    adantr
    @52
    @25
    @51
    wa
    cU
    cV
    @46
    cdif
    wcel
    @3
    @25
    @51
    wph
    @25
    @2
    trlsegvdeg.u
    adantr
    anim1i
    cU
    cV
    @0
    eldifsn
    sylibr
    1loopgrvd0
    syl5breqr
    pm2.61dane
    c2
    @5
    @13
    dvdsadd2b
    syl112anc
    wph
    @28
    @15
    wb
    @2
    wph
    @27
    @14
    c2
    cdvds
    wph
    @13
    @5
    wph
    @13
    @34
    nn0cnd
    wph
    @5
    @33
    nn0cnd
    addcomd
    breq2d
    adantr
    bitrd
    notbid
    @3
    @11
    @18
    cU
    @3
    @9
    @16
    @10
    @17
    c0
    @3
    @0
    @1
    @8
    wph
    @2
    simpr
    #
    eqeq2d
    @3
    @0
    @1
    @8
    @56
    preq2d
    ifbieq2d
    eleq2d
    3bitr3d
end
