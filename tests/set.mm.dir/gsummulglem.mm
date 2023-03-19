include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "cabl.mm"
include "cmhm.mm"
include "cn0.mm"
include "cz.mm"
include "wi.mm"
include "wa.mm"
include "cghm.mm"
include "mulgghm.mm"
include "ghmmhm.mm"
include "expcom.mm"
include "mulgmhm.mm"
include "ex.mm"
include "mpjaod.mm"
include "oveq2.mm"
include "gsummhm2.mm"

theorem gsummulglem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume gsummulg.b: |- B = ( Base ` G )
  assume gsummulg.z: |- .0. = ( 0g ` G )
  assume gsummulg.t: |- .x. = ( .g ` G )
  assume gsummulg.a: |- ( ph -> A e. V )
  assume gsummulg.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsummulg.w: |- ( ph -> ( k e. A |-> X ) finSupp .0. )
  assume gsummulglem.g: |- ( ph -> G e. CMnd )
  assume gsummulglem.n: |- ( ph -> N e. ZZ )
  assume gsummulglem.o: |- ( ph -> ( G e. Abel \/ N e. NN0 ) )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint k ph
  disjoint .x. k
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint G x
  disjoint N x
  disjoint .x. x
  disjoint X x
  assert |- ( ph -> ( G gsum ( k e. A |-> ( N .x. X ) ) ) = ( N .x. ( G gsum ( k e. A |-> X ) ) ) )

  proof
    wph
    vx
    cA
    cB
    cN
    vx
    cv
    #
    c.x
    co
    #
    cN
    cX
    c.x
    co
    vk
    cN
    cG
    vk
    cA
    cX
    cmpt
    cgsu
    co
    #
    c.x
    co
    cG
    cG
    cV
    cX
    c.0
    gsummulg.b
    gsummulg.z
    gsummulglem.g
    wph
    cG
    ccmn
    wcel
    #
    cG
    cmnd
    wcel
    gsummulglem.g
    cG
    cmnmnd
    syl
    gsummulg.a
    wph
    cG
    cabl
    wcel
    #
    vx
    cB
    @1
    cmpt
    #
    cG
    cG
    cmhm
    co
    wcel
    #
    cN
    cn0
    wcel
    #
    wph
    cN
    cz
    wcel
    #
    @4
    @6
    wi
    gsummulglem.n
    @4
    @8
    @6
    @4
    @8
    wa
    @5
    cG
    cG
    cghm
    co
    wcel
    @6
    vx
    cB
    c.x
    cG
    cN
    gsummulg.b
    gsummulg.t
    mulgghm
    cG
    cG
    @5
    ghmmhm
    syl
    expcom
    syl
    wph
    @3
    @7
    @6
    wi
    gsummulglem.g
    @3
    @7
    @6
    vx
    cB
    c.x
    cG
    cN
    gsummulg.b
    gsummulg.t
    mulgmhm
    ex
    syl
    gsummulglem.o
    mpjaod
    gsummulg.f
    gsummulg.w
    @0
    cX
    cN
    c.x
    oveq2
    @0
    @2
    cN
    c.x
    oveq2
    gsummhm2
end
