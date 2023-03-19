include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "c2.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "wcel.mm"
include "cvv.mm"
include "ciedg.mm"
include "cop.mm"
include "csn.mm"
include "3ad2ant1.mm"
include "cvtx.mm"
include "fvexd.mm"
include "wnel.mm"
include "wi.mm"
include "simpl.mm"
include "adantl.mm"
include "simpr.mm"
include "nelprd.mm"
include "df-nel.mm"
include "sylibr.mm"
include "neleq2.mm"
include "syl5ibr.mm"
include "expd.mm"
include "syl.mm"
include "3imp.mm"
include "1hevtxdg0.mm"
include "oveq2d.mm"
include "eupth2lem3lem1.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "notbid.mm"
include "wb.mm"
include "cv.mm"
include "crab.mm"
include "fveq2.mm"
include "elrab3.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "wo.mm"
include "3ad2ant3.mm"
include "2thd.mm"
include "neeq1.mm"
include "bibi12d.mm"
include "syl5ibcom.mm"
include "pm5.32rd.mm"
include "neneqd.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "3bitr3d.mm"
include "eupth2lem1.mm"
include "3bitr4d.mm"
include "3bitrd.mm"

theorem eupth2lem3lem6
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
  assume eupth2lem3.e: |- ( ph -> ( I ` ( F ` N ) ) = { ( P ` N ) , ( P ` ( N + 1 ) ) } )

  disjoint U x
  disjoint V x
  disjoint X x
  assert |- ( ( ph /\ ( P ` N ) =/= ( P ` ( N + 1 ) ) /\ ( U =/= ( P ` N ) /\ U =/= ( P ` ( N + 1 ) ) ) ) -> ( -. 2 || ( ( ( VtxDeg ` X ) ` U ) + ( ( VtxDeg ` Y ) ` U ) ) <-> U e. if ( ( P ` 0 ) = ( P ` ( N + 1 ) ) , (/) , { ( P ` 0 ) , ( P ` ( N + 1 ) ) } ) ) )

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
    wne
    #
    cU
    @0
    wne
    #
    cU
    @1
    wne
    #
    wa
    #
    w3a
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
    c2
    @8
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
    c0
    @14
    @0
    cpr
    cif
    #
    wcel
    #
    cU
    @14
    @1
    wceq
    c0
    @14
    @1
    cpr
    cif
    wcel
    #
    @6
    @11
    @12
    @6
    @10
    @8
    c2
    cdvds
    @6
    @10
    @8
    cc0
    caddc
    co
    #
    @8
    @6
    @9
    cc0
    @8
    caddc
    @6
    cN
    cF
    cfv
    #
    cU
    @19
    cI
    cfv
    #
    cY
    cV
    cvv
    cvv
    wph
    @2
    cY
    ciedg
    cfv
    @19
    @20
    cop
    csn
    wceq
    @5
    trlsegvdeg.iy
    3ad2ant1
    wph
    @2
    cY
    cvtx
    cfv
    cV
    wceq
    @5
    trlsegvdeg.vy
    3ad2ant1
    @6
    cN
    cF
    fvexd
    wph
    @2
    cU
    cV
    wcel
    #
    @5
    trlsegvdeg.u
    3ad2ant1
    #
    @6
    @19
    cI
    fvexd
    wph
    @2
    @5
    cU
    @20
    wnel
    #
    wph
    @20
    @0
    @1
    cpr
    #
    wceq
    #
    @2
    @5
    @23
    wi
    wi
    eupth2lem3.e
    @25
    @2
    @5
    @23
    @2
    @5
    wa
    #
    @23
    @25
    cU
    @24
    wnel
    #
    @26
    cU
    @24
    wcel
    wn
    @27
    @26
    cU
    @0
    @1
    @5
    @3
    @2
    @3
    @4
    simpl
    #
    adantl
    @5
    @4
    @2
    @3
    @4
    simpr
    #
    adantl
    nelprd
    cU
    @24
    df-nel
    sylibr
    @20
    @24
    cU
    neleq2
    syl5ibr
    expd
    syl
    3imp
    1hevtxdg0
    oveq2d
    wph
    @2
    @18
    @8
    wceq
    @5
    wph
    @8
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
    nn0cnd
    addid1d
    3ad2ant1
    eqtrd
    breq2d
    notbid
    wph
    @2
    @13
    @16
    wb
    @5
    wph
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
    @13
    @16
    wph
    @21
    @35
    @13
    wb
    trlsegvdeg.u
    @33
    @13
    vx
    cU
    cV
    @30
    cU
    wceq
    #
    @32
    @12
    @36
    @31
    @8
    c2
    cdvds
    @30
    cU
    @7
    fveq2
    breq2d
    notbid
    elrab3
    syl
    wph
    @34
    @15
    cU
    eupth2lem3.o
    eleq2d
    bitr3d
    3ad2ant1
    @6
    @14
    @0
    wne
    #
    cU
    @14
    wceq
    #
    cU
    @0
    wceq
    #
    wo
    #
    wa
    #
    @14
    @1
    wne
    #
    @38
    cU
    @1
    wceq
    #
    wo
    #
    wa
    #
    @16
    @17
    @6
    @37
    @38
    wa
    @42
    @38
    wa
    @41
    @45
    @6
    @38
    @37
    @42
    @6
    @3
    @4
    wb
    @38
    @37
    @42
    wb
    @6
    @3
    @4
    @5
    wph
    @3
    @2
    @28
    3ad2ant3
    #
    @5
    wph
    @4
    @2
    @29
    3ad2ant3
    #
    2thd
    @38
    @3
    @37
    @4
    @42
    cU
    @14
    @0
    neeq1
    cU
    @14
    @1
    neeq1
    bibi12d
    syl5ibcom
    pm5.32rd
    @6
    @38
    @40
    @37
    @6
    @38
    @39
    @38
    wo
    #
    @40
    @6
    @39
    wn
    @38
    @48
    wb
    @6
    cU
    @0
    @46
    neneqd
    @39
    @38
    biorf
    syl
    @39
    @38
    orcom
    syl6bb
    anbi2d
    @6
    @38
    @44
    @42
    @6
    @38
    @43
    @38
    wo
    #
    @44
    @6
    @43
    wn
    @38
    @49
    wb
    @6
    cU
    @1
    @47
    neneqd
    @43
    @38
    biorf
    syl
    @43
    @38
    orcom
    syl6bb
    anbi2d
    3bitr3d
    @6
    @21
    @16
    @41
    wb
    @22
    @14
    @0
    cU
    cV
    eupth2lem1
    syl
    @6
    @21
    @17
    @45
    wb
    @22
    @14
    @1
    cU
    cV
    eupth2lem1
    syl
    3bitr4d
    3bitrd
end
