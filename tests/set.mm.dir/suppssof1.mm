include "cof.mm"
include "co.mm"
include "csupp.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "oveq1d.mm"
include "cvv.mm"
include "feqmptd.mm"
include "eqsstr3d.mm"
include "fvexd.mm"
include "ffvelrnda.mm"
include "suppssov1.mm"
include "eqsstrd.mm"

theorem suppssof1
  let wph: wff ph
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let cL: class L
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  assume suppssof1.s: |- ( ph -> ( A supp Y ) C_ L )
  assume suppssof1.o: |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z )
  assume suppssof1.a: |- ( ph -> A : D --> V )
  assume suppssof1.b: |- ( ph -> B : D --> R )
  assume suppssof1.d: |- ( ph -> D e. W )
  assume suppssof1.y: |- ( ph -> Y e. U )

  disjoint ph v
  disjoint B v
  disjoint O v
  disjoint R v
  disjoint Y v
  disjoint Z v
  disjoint ph x
  disjoint v x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint O x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( ( A oF O B ) supp Z ) C_ L )

  proof
    wph
    cA
    cB
    cO
    cof
    co
    #
    cZ
    csupp
    co
    vx
    cD
    vx
    cv
    #
    cA
    cfv
    #
    @1
    cB
    cfv
    #
    cO
    co
    cmpt
    #
    cZ
    csupp
    co
    cL
    wph
    @0
    @4
    cZ
    csupp
    wph
    vx
    cD
    cD
    @2
    @3
    cO
    cD
    cA
    cB
    cW
    cW
    wph
    cD
    cV
    cA
    wf
    cA
    cD
    wfn
    suppssof1.a
    cD
    cV
    cA
    ffn
    syl
    wph
    cD
    cR
    cB
    wf
    cB
    cD
    wfn
    suppssof1.b
    cD
    cR
    cB
    ffn
    syl
    suppssof1.d
    suppssof1.d
    cD
    inidm
    wph
    @1
    cD
    wcel
    wa
    #
    @2
    eqidd
    @5
    @3
    eqidd
    offval
    oveq1d
    wph
    vx
    vv
    @2
    @3
    cD
    cR
    cL
    cO
    cvv
    cU
    cY
    cZ
    wph
    vx
    cD
    @2
    cmpt
    #
    cY
    csupp
    co
    cA
    cY
    csupp
    co
    cL
    wph
    cA
    @6
    cY
    csupp
    wph
    vx
    cD
    cV
    cA
    suppssof1.a
    feqmptd
    oveq1d
    suppssof1.s
    eqsstr3d
    suppssof1.o
    @5
    @1
    cA
    fvexd
    wph
    cD
    cR
    @1
    cB
    suppssof1.b
    ffvelrnda
    suppssof1.y
    suppssov1
    eqsstrd
end
