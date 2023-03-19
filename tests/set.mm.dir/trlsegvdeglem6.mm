include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "cfn.mm"
include "trlsegvdeglem4.mm"
include "wcel.mm"
include "wfun.mm"
include "ctrls.mm"
include "wbr.mm"
include "chash.mm"
include "wf1.mm"
include "trlf1.mm"
include "f1fun.mm"
include "3syl.mm"
include "fzofi.mm"
include "imafi.mm"
include "sylancl.mm"
include "infi.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem trlsegvdeglem6
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


  assert |- ( ph -> dom ( iEdg ` X ) e. Fin )

  proof
    wph
    cX
    ciedg
    cfv
    cdm
    cF
    cc0
    cN
    cfzo
    co
    #
    cima
    #
    cI
    cdm
    #
    cin
    #
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
    trlsegvdeglem4
    wph
    @1
    cfn
    wcel
    #
    @3
    cfn
    wcel
    wph
    cF
    wfun
    #
    @0
    cfn
    wcel
    @4
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    @2
    cF
    wf1
    @5
    trlsegvdeg.w
    cP
    cF
    cG
    cI
    trlsegvdeg.i
    trlf1
    @6
    @2
    cF
    f1fun
    3syl
    cc0
    cN
    fzofi
    cF
    @0
    imafi
    sylancl
    @1
    @2
    infi
    syl
    eqeltrd
end
