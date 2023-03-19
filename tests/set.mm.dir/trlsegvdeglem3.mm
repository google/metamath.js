include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "cop.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "funsng.mm"
include "mp1i.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem trlsegvdeglem3
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


  assert |- ( ph -> Fun ( iEdg ` Y ) )

  proof
    wph
    cY
    ciedg
    cfv
    #
    wfun
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
    wfun
    #
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    @4
    wph
    @5
    @6
    cN
    cF
    fvex
    @1
    cI
    fvex
    pm3.2i
    @1
    @2
    cvv
    cvv
    funsng
    mp1i
    wph
    @0
    @3
    trlsegvdeg.iy
    funeqd
    mpbird
end
