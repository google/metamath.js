include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "ellkr.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem ellkr2
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  assume lkrfval2.v: |- V = ( Base ` W )
  assume lkrfval2.d: |- D = ( Scalar ` W )
  assume lkrfval2.o: |- .0. = ( 0g ` D )
  assume lkrfval2.f: |- F = ( LFnl ` W )
  assume lkrfval2.k: |- K = ( LKer ` W )
  assume ellkr2.w: |- ( ph -> W e. Y )
  assume ellkr2.g: |- ( ph -> G e. F )
  assume ellkr2.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( X e. ( K ` G ) <-> ( G ` X ) = .0. ) )

  proof
    wph
    cX
    cG
    cK
    cfv
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    cG
    cfv
    c.0
    wceq
    #
    wa
    #
    @2
    wph
    cW
    cY
    wcel
    cG
    cF
    wcel
    @0
    @3
    wb
    ellkr2.w
    ellkr2.g
    cD
    cF
    cG
    cK
    cV
    cW
    cX
    cY
    c.0
    lkrfval2.v
    lkrfval2.d
    lkrfval2.o
    lkrfval2.f
    lkrfval2.k
    ellkr
    syl2anc
    wph
    @1
    @2
    ellkr2.x
    biantrurd
    bitr4d
end
