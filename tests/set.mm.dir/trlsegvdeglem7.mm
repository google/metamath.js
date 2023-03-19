include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "csn.mm"
include "cfn.mm"
include "trlsegvdeglem5.mm"
include "snfi.mm"
include "syl6eqel.mm"

theorem trlsegvdeglem7
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


  assert |- ( ph -> dom ( iEdg ` Y ) e. Fin )

  proof
    wph
    cY
    ciedg
    cfv
    cdm
    cN
    cF
    cfv
    #
    csn
    cfn
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
    trlsegvdeglem5
    @0
    snfi
    syl6eqel
end
