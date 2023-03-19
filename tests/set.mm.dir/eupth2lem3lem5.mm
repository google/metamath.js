include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "trlsegvdeglem1.mm"
include "prelpwi.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem eupth2lem3lem5
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
  assert |- ( ph -> ( I ` ( F ` N ) ) e. ~P V )

  proof
    wph
    cN
    cF
    cfv
    cI
    cfv
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
    cpr
    #
    cV
    cpw
    #
    eupth2lem3.e
    wph
    @0
    cV
    wcel
    @1
    cV
    wcel
    wa
    @2
    @3
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
    @0
    @1
    cV
    prelpwi
    syl
    eqeltrd
end
