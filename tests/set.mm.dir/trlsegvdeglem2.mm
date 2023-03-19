include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "funres.mm"
include "syl.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem trlsegvdeglem2
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


  assert |- ( ph -> Fun ( iEdg ` X ) )

  proof
    wph
    cX
    ciedg
    cfv
    #
    wfun
    cI
    cF
    cc0
    cN
    cfzo
    co
    cima
    #
    cres
    #
    wfun
    #
    wph
    cI
    wfun
    @3
    trlsegvdeg.f
    @1
    cI
    funres
    syl
    wph
    @0
    @2
    trlsegvdeg.ix
    funeqd
    mpbird
end
