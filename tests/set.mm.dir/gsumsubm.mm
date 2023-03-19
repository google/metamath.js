include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cmnd.mm"
include "c0g.mm"
include "eqid.mm"
include "csubmnd.mm"
include "wcel.mm"
include "submrcl.mm"
include "syl.mm"
include "wss.mm"
include "submss.mm"
include "subm0cl.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "mndlrid.mm"
include "sylan.mm"
include "gsumress.mm"

theorem gsumsubm
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vx: setvar x
  assume gsumsubm.a: |- ( ph -> A e. V )
  assume gsumsubm.s: |- ( ph -> S e. ( SubMnd ` G ) )
  assume gsumsubm.f: |- ( ph -> F : A --> S )
  assume gsumsubm.h: |- H = ( G |`s S )


  assert |- ( ph -> ( G gsum F ) = ( H gsum F ) )

  proof
    wph
    vx
    cA
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    cS
    cF
    cG
    cH
    cmnd
    cV
    cG
    c0g
    cfv
    #
    @0
    eqid
    #
    @1
    eqid
    #
    gsumsubm.h
    wph
    cS
    cG
    csubmnd
    cfv
    wcel
    #
    cG
    cmnd
    wcel
    #
    gsumsubm.s
    cS
    cG
    submrcl
    syl
    #
    gsumsubm.a
    wph
    @5
    cS
    @0
    wss
    gsumsubm.s
    @0
    cS
    cG
    @3
    submss
    syl
    gsumsubm.f
    wph
    @5
    @2
    cS
    wcel
    gsumsubm.s
    cS
    cG
    @2
    @2
    eqid
    #
    subm0cl
    syl
    wph
    @6
    vx
    cv
    #
    @0
    wcel
    @2
    @9
    @1
    co
    @9
    wceq
    @9
    @2
    @1
    co
    @9
    wceq
    wa
    @7
    @0
    @1
    cG
    @9
    @2
    @3
    @4
    @8
    mndlrid
    sylan
    gsumress
end
