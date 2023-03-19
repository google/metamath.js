include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cmin.mm"
include "cfzo.mm"
include "cop.mm"
include "csubstr.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "swrdval2.mm"
include "fveq1d.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem swrdfv
  let cA: class A
  let cS: class S
  let cF: class F
  let cL: class L
  let cX: class X
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cV: class V


  assert |- ( ( ( S e. Word A /\ F e. ( 0 ... L ) /\ L e. ( 0 ... ( # ` S ) ) ) /\ X e. ( 0 ..^ ( L - F ) ) ) -> ( ( S substr <. F , L >. ) ` X ) = ( S ` ( X + F ) ) )

  proof
    cS
    cA
    cword
    wcel
    cF
    cc0
    cL
    cfz
    co
    wcel
    cL
    cc0
    cS
    chash
    cfv
    cfz
    co
    wcel
    w3a
    #
    cX
    cc0
    cL
    cF
    cmin
    co
    cfzo
    co
    #
    wcel
    cX
    cS
    cF
    cL
    cop
    csubstr
    co
    #
    cfv
    cX
    vx
    @1
    vx
    cv
    #
    cF
    caddc
    co
    #
    cS
    cfv
    #
    cmpt
    #
    cfv
    cX
    cF
    caddc
    co
    #
    cS
    cfv
    #
    @0
    cX
    @2
    @6
    vx
    cA
    cS
    cF
    cL
    swrdval2
    fveq1d
    vx
    cX
    @5
    @8
    @1
    @6
    @3
    cX
    wceq
    @4
    @7
    cS
    @3
    cX
    cF
    caddc
    oveq1
    fveq2d
    @6
    eqid
    @7
    cS
    fvex
    fvmpt
    sylan9eq
end
