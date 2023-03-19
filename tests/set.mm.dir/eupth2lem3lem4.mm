include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
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
include "wa.mm"
include "wi.mm"
include "cvv.mm"
include "fvexd.mm"
include "ad2antrr.mm"
include "trlsegvdeglem1.mm"
include "simprd.mm"
include "neeq1.mm"
include "biimpcd.mm"
include "adantl.mm"
include "imp.mm"
include "cpw.mm"
include "ciedg.mm"
include "cop.mm"
include "csn.mm"
include "wss.mm"
include "wif.mm"
include "adantr.mm"
include "df-ne.mm"
include "ifpfal.mm"
include "sylbi.mm"
include "preq1.mm"
include "sseq1d.mm"
include "syl6bi.mm"
include "mpd.mm"
include "cvtx.mm"
include "1hegrvtxdg1.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "notbid.mm"
include "cv.mm"
include "crab.mm"
include "cz.mm"
include "cn.mm"
include "clt.mm"
include "eupth2lem3lem1.mm"
include "nn0zd.mm"
include "2nn.mm"
include "a1i.mm"
include "1lt2.mm"
include "ndvdsp1.mm"
include "syl3anc.mm"
include "con2d.mm"
include "1z.mm"
include "n2dvds1.mm"
include "opoe.mm"
include "mpanr12.mm"
include "ex.mm"
include "syl.mm"
include "impbid.mm"
include "fveq2.mm"
include "elrab3.mm"
include "eleq2d.mm"
include "3bitr2d.mm"
include "fvex.mm"
include "eupth2lem2.mm"
include "adantll.mm"
include "3bitrd.mm"
include "expcom.mm"
include "eqcoms.mm"
include "simpld.mm"
include "neeq2.mm"
include "preq2.mm"
include "1hegrvtxdg1r.mm"
include "necom.mm"
include "sylanb.mm"
include "con1bid.mm"
include "jaoi.mm"
include "com12.mm"
include "3impia.mm"

theorem eupth2lem3lem4
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
  assume eupth2lem3lem4.i: |- ( ph -> ( I ` ( F ` N ) ) e. ~P V )

  disjoint U x
  disjoint V x
  disjoint X x
  assert |- ( ( ph /\ ( P ` N ) =/= ( P ` ( N + 1 ) ) /\ ( U = ( P ` N ) \/ U = ( P ` ( N + 1 ) ) ) ) -> ( -. 2 || ( ( ( VtxDeg ` X ) ` U ) + ( ( VtxDeg ` Y ) ` U ) ) <-> U e. if ( ( P ` 0 ) = ( P ` ( N + 1 ) ) , (/) , { ( P ` 0 ) , ( P ` ( N + 1 ) ) } ) ) )

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
    #
    cP
    cfv
    #
    wne
    #
    cU
    @0
    wceq
    #
    cU
    @2
    wceq
    #
    wo
    #
    c2
    cU
    cX
    cvtxdg
    cfv
    #
    cfv
    #
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
    #
    cU
    cc0
    cP
    cfv
    #
    @2
    wceq
    c0
    @13
    @2
    cpr
    cif
    wcel
    #
    wb
    #
    @6
    wph
    @3
    wa
    #
    @15
    @4
    @16
    @15
    wi
    #
    @5
    @17
    @0
    cU
    @16
    @0
    cU
    wceq
    #
    @15
    @16
    @18
    wa
    #
    @12
    c2
    @8
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    #
    cU
    @13
    @0
    wceq
    c0
    @13
    @0
    cpr
    cif
    #
    wcel
    #
    wn
    #
    @14
    @19
    @11
    @21
    @19
    @10
    @20
    c2
    cdvds
    @19
    @9
    c1
    @8
    caddc
    @19
    cN
    cF
    cfv
    #
    cU
    @2
    @26
    cI
    cfv
    #
    cY
    cV
    cvv
    @19
    cN
    cF
    fvexd
    wph
    cU
    cV
    wcel
    #
    @3
    @18
    trlsegvdeg.u
    ad2antrr
    wph
    @2
    cV
    wcel
    #
    @3
    @18
    wph
    @0
    cV
    wcel
    #
    @29
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
    #
    simprd
    ad2antrr
    @16
    @18
    cU
    @2
    wne
    #
    @3
    @18
    @32
    wi
    wph
    @18
    @3
    @32
    @0
    cU
    @2
    neeq1
    biimpcd
    adantl
    imp
    wph
    @27
    cV
    cpw
    wcel
    #
    @3
    @18
    eupth2lem3lem4.i
    ad2antrr
    wph
    cY
    ciedg
    cfv
    @26
    @27
    cop
    csn
    wceq
    #
    @3
    @18
    trlsegvdeg.iy
    ad2antrr
    @16
    @18
    cU
    @2
    cpr
    #
    @27
    wss
    #
    @16
    @0
    @2
    wceq
    #
    @27
    @0
    csn
    wceq
    #
    @0
    @2
    cpr
    #
    @27
    wss
    #
    wif
    #
    @18
    @36
    wi
    #
    wph
    @41
    @3
    eupth2lem3lem3.e
    adantr
    #
    @16
    @41
    @40
    @42
    @3
    @41
    @40
    wb
    #
    wph
    @3
    @37
    wn
    @44
    @0
    @2
    df-ne
    @37
    @38
    @40
    ifpfal
    sylbi
    adantl
    #
    @18
    @40
    @36
    @18
    @39
    @35
    @27
    @0
    cU
    @2
    preq1
    sseq1d
    biimpcd
    syl6bi
    mpd
    imp
    wph
    cY
    cvtx
    cfv
    cV
    wceq
    #
    @3
    @18
    trlsegvdeg.vy
    ad2antrr
    1hegrvtxdg1
    oveq2d
    breq2d
    notbid
    wph
    @22
    @25
    wb
    #
    @3
    @18
    wph
    @21
    @24
    wph
    @21
    c2
    @8
    cdvds
    wbr
    #
    wn
    #
    cU
    c2
    vx
    cv
    #
    @7
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
    @24
    wph
    @21
    @49
    wph
    @48
    @21
    wph
    @8
    cz
    wcel
    #
    c2
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @48
    @22
    wi
    wph
    @8
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
    nn0zd
    #
    @57
    wph
    2nn
    a1i
    @58
    wph
    1lt2
    a1i
    c2
    @8
    ndvdsp1
    syl3anc
    con2d
    wph
    @56
    @49
    @21
    wi
    @59
    @56
    @49
    @21
    @56
    @49
    wa
    c1
    cz
    wcel
    c2
    c1
    cdvds
    wbr
    wn
    @21
    1z
    n2dvds1
    @8
    c1
    opoe
    mpanr12
    ex
    syl
    impbid
    wph
    @28
    @55
    @49
    wb
    trlsegvdeg.u
    @53
    @49
    vx
    cU
    cV
    @50
    cU
    wceq
    #
    @52
    @48
    @60
    @51
    @8
    c2
    cdvds
    @50
    cU
    @7
    fveq2
    breq2d
    notbid
    elrab3
    syl
    wph
    @54
    @23
    cU
    eupth2lem3.o
    eleq2d
    3bitr2d
    notbid
    #
    ad2antrr
    @3
    @18
    @25
    @14
    wb
    #
    wph
    @13
    @0
    @2
    cU
    cN
    cP
    fvex
    eupth2lem2
    adantll
    3bitrd
    expcom
    eqcoms
    @17
    @2
    cU
    @16
    @2
    cU
    wceq
    #
    @15
    @16
    @63
    wa
    #
    @12
    @22
    @25
    @14
    @64
    @11
    @21
    @64
    @10
    @20
    c2
    cdvds
    @64
    @9
    c1
    @8
    caddc
    @64
    @26
    @0
    cU
    @27
    cY
    cV
    cvv
    @64
    cN
    cF
    fvexd
    wph
    @30
    @3
    @63
    wph
    @30
    @29
    @31
    simpld
    ad2antrr
    wph
    @28
    @3
    @63
    trlsegvdeg.u
    ad2antrr
    @16
    @63
    @0
    cU
    wne
    #
    @3
    @63
    @65
    wi
    wph
    @63
    @3
    @65
    @2
    cU
    @0
    neeq2
    biimpcd
    adantl
    imp
    wph
    @33
    @3
    @63
    eupth2lem3lem4.i
    ad2antrr
    wph
    @34
    @3
    @63
    trlsegvdeg.iy
    ad2antrr
    @16
    @63
    @0
    cU
    cpr
    #
    @27
    wss
    #
    @16
    @41
    @63
    @67
    wi
    #
    @43
    @16
    @41
    @40
    @68
    @45
    @63
    @40
    @67
    @63
    @39
    @66
    @27
    @2
    cU
    @0
    preq2
    sseq1d
    biimpcd
    syl6bi
    mpd
    imp
    wph
    @46
    @3
    @63
    trlsegvdeg.vy
    ad2antrr
    1hegrvtxdg1r
    oveq2d
    breq2d
    notbid
    wph
    @47
    @3
    @63
    @61
    ad2antrr
    @3
    @63
    @62
    wph
    @3
    @63
    wa
    @14
    @24
    @3
    @2
    @0
    wne
    @63
    @14
    wn
    @24
    wb
    @0
    @2
    necom
    @13
    @2
    @0
    cU
    @1
    cP
    fvex
    eupth2lem2
    sylanb
    con1bid
    adantll
    3bitrd
    expcom
    eqcoms
    jaoi
    com12
    3impia
end
