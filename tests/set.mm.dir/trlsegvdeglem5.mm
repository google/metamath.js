include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cop.mm"
include "csn.mm"
include "dmeqd.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "dmsnopg.mm"
include "mp1i.mm"
include "eqtrd.mm"

theorem trlsegvdeglem5
  let wph: wff ph
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


  assert |- ( ph -> dom ( iEdg ` Y ) = { ( F ` N ) } )

  proof
    wph
    cY
    ciedg
    cfv
    #
    cdm
    cN
    cF
    cfv
    #
    @1
    cI
    cfv
    #
    cop
    csn
    #
    cdm
    #
    @1
    csn
    #
    wph
    @0
    @3
    trlsegvdeg.iy
    dmeqd
    @2
    cvv
    wcel
    @4
    @5
    wceq
    wph
    @1
    cI
    fvex
    @1
    @2
    cvv
    dmsnopg
    mp1i
    eqtrd
end
