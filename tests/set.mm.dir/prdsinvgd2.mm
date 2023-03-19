include "cfv.mm"
include "cv.mm"
include "cminusg.mm"
include "cmpt.mm"
include "prdsinvgd.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem prdsinvgd2
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume prdsinvgd2.y: |- Y = ( S Xs_ R )
  assume prdsinvgd2.i: |- ( ph -> I e. W )
  assume prdsinvgd2.s: |- ( ph -> S e. V )
  assume prdsinvgd2.r: |- ( ph -> R : I --> Grp )
  assume prdsinvgd2.b: |- B = ( Base ` Y )
  assume prdsinvgd2.n: |- N = ( invg ` Y )
  assume prdsinvgd2.x: |- ( ph -> X e. B )
  assume prdsinvgd2.j: |- ( ph -> J e. I )


  assert |- ( ph -> ( ( N ` X ) ` J ) = ( ( invg ` ( R ` J ) ) ` ( X ` J ) ) )

  proof
    wph
    cJ
    cX
    cN
    cfv
    #
    cfv
    cJ
    vx
    cI
    vx
    cv
    #
    cX
    cfv
    #
    @1
    cR
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    cJ
    cX
    cfv
    #
    cJ
    cR
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    wph
    cJ
    @0
    @6
    wph
    vx
    cB
    cR
    cS
    cI
    cN
    cV
    cW
    cX
    cY
    prdsinvgd2.y
    prdsinvgd2.i
    prdsinvgd2.s
    prdsinvgd2.r
    prdsinvgd2.b
    prdsinvgd2.n
    prdsinvgd2.x
    prdsinvgd
    fveq1d
    wph
    cJ
    cI
    wcel
    @7
    @11
    wceq
    prdsinvgd2.j
    vx
    cJ
    @5
    @11
    cI
    @6
    @1
    cJ
    wceq
    #
    @2
    @8
    @4
    @10
    @12
    @3
    @9
    cminusg
    @1
    cJ
    cR
    fveq2
    fveq2d
    @1
    cJ
    cX
    fveq2
    fveq12d
    @6
    eqid
    @8
    @10
    fvex
    fvmpt
    syl
    eqtrd
end
