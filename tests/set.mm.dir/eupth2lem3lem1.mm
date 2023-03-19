include "cvtx.mm"
include "cfv.mm"
include "cn0.mm"
include "cvtxdg.mm"
include "cvv.mm"
include "wcel.mm"
include "ciedg.mm"
include "cdm.mm"
include "cfn.mm"
include "wf.mm"
include "eleqtrrd.mm"
include "elfvexd.mm"
include "trlsegvdeglem6.mm"
include "eqid.mm"
include "vtxdgfisf.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"

theorem eupth2lem3lem1
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


  assert |- ( ph -> ( ( VtxDeg ` X ) ` U ) e. NN0 )

  proof
    wph
    cX
    cvtx
    cfv
    #
    cn0
    cU
    cX
    cvtxdg
    cfv
    #
    wph
    cX
    cvv
    wcel
    cX
    ciedg
    cfv
    #
    cdm
    #
    cfn
    wcel
    @0
    cn0
    @1
    wf
    wph
    cU
    cvtx
    cX
    wph
    cU
    cV
    @0
    trlsegvdeg.u
    trlsegvdeg.vx
    eleqtrrd
    #
    elfvexd
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
    trlsegvdeglem6
    @3
    cX
    @2
    @0
    cvv
    @0
    eqid
    @2
    eqid
    @3
    eqid
    vtxdgfisf
    syl2anc
    @4
    ffvelrnd
end
