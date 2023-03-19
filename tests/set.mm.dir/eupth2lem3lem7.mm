include "c2.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "wceq.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "wcel.mm"
include "trlsegvdeg.mm"
include "breq2d.mm"
include "notbid.mm"
include "wb.mm"
include "csn.mm"
include "wss.mm"
include "wif.mm"
include "ifpprsnss.mm"
include "syl.mm"
include "eupth2lem3lem3.mm"
include "wo.mm"
include "wne.mm"
include "wa.mm"
include "wi.mm"
include "eupth2lem3lem5.mm"
include "eupth2lem3lem4.mm"
include "3expa.mm"
include "expcom.mm"
include "neanior.mm"
include "eupth2lem3lem6.mm"
include "sylbir.mm"
include "pm2.61i.mm"
include "pm2.61dane.mm"
include "bitrd.mm"

theorem eupth2lem3lem7
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
  assert |- ( ph -> ( -. 2 || ( ( VtxDeg ` Z ) ` U ) <-> U e. if ( ( P ` 0 ) = ( P ` ( N + 1 ) ) , (/) , { ( P ` 0 ) , ( P ` ( N + 1 ) ) } ) ) )

  proof
    wph
    c2
    cU
    cZ
    cvtxdg
    cfv
    cfv
    #
    cdvds
    wbr
    #
    wn
    c2
    cU
    cX
    cvtxdg
    cfv
    cfv
    cU
    cY
    cvtxdg
    cfv
    cfv
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
    cN
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    c0
    @5
    @6
    cpr
    cif
    wcel
    #
    wph
    @1
    @3
    wph
    @0
    @2
    c2
    cdvds
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
    trlsegvdeg
    breq2d
    notbid
    wph
    @4
    @7
    wb
    #
    cN
    cP
    cfv
    #
    @6
    wph
    vx
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
    eupth2lem3.o
    wph
    cN
    cF
    cfv
    cI
    cfv
    #
    @9
    @6
    cpr
    #
    wceq
    @9
    @6
    wceq
    @10
    @9
    csn
    wceq
    @11
    @10
    wss
    wif
    eupth2lem3.e
    @9
    @6
    @10
    ifpprsnss
    syl
    #
    eupth2lem3lem3
    cU
    @9
    wceq
    cU
    @6
    wceq
    wo
    #
    wph
    @9
    @6
    wne
    #
    wa
    #
    @8
    wi
    #
    @15
    @13
    @8
    wph
    @14
    @13
    @8
    wph
    vx
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
    eupth2lem3.o
    @12
    wph
    vx
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
    eupth2lem3.o
    eupth2lem3.e
    eupth2lem3lem5
    eupth2lem3lem4
    3expa
    expcom
    @13
    wn
    cU
    @9
    wne
    cU
    @6
    wne
    wa
    #
    @16
    cU
    @9
    cU
    @6
    neanior
    @15
    @17
    @8
    wph
    @14
    @17
    @8
    wph
    vx
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
    eupth2lem3.o
    eupth2lem3.e
    eupth2lem3lem6
    3expa
    expcom
    sylbir
    pm2.61i
    pm2.61dane
    bitrd
end
