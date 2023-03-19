include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "cpw.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "mrcfval.mm"
include "adantr.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "adantl.mm"
include "wb.mm"
include "mre1cl.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "intex.mm"
include "sylib.mm"
include "fvmptd.mm"

theorem mrcval
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vx: setvar x
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )

  disjoint F s
  disjoint C s
  disjoint X s
  disjoint U s
  disjoint F c
  disjoint F x
  disjoint c x
  disjoint c s
  disjoint s x
  disjoint C c
  disjoint C x
  disjoint X c
  disjoint X x
  disjoint U c
  disjoint U x
  disjoint V c
  disjoint V x
  disjoint V s
  assert |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> ( F ` U ) = |^| { s e. C | U C_ s } )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cX
    wss
    #
    wa
    #
    vx
    cU
    vx
    cv
    #
    vs
    cv
    #
    wss
    #
    vs
    cC
    crab
    #
    cint
    #
    cU
    @4
    wss
    #
    vs
    cC
    crab
    #
    cint
    #
    cX
    cpw
    #
    cF
    cvv
    @0
    cF
    vx
    @11
    @7
    cmpt
    wceq
    @1
    vx
    cC
    cF
    cX
    vs
    mrcfval.f
    mrcfval
    adantr
    @3
    cU
    wceq
    #
    @7
    @10
    wceq
    @2
    @12
    @6
    @9
    @12
    @5
    @8
    vs
    cC
    @3
    cU
    @4
    sseq1
    rabbidv
    inteqd
    adantl
    @0
    cU
    @11
    wcel
    #
    @1
    @0
    cX
    cC
    wcel
    #
    @13
    @1
    wb
    cC
    cX
    mre1cl
    #
    cU
    cX
    cC
    elpw2g
    syl
    biimpar
    @2
    @9
    c0
    wne
    #
    @10
    cvv
    wcel
    @2
    cX
    @9
    wcel
    #
    @16
    @2
    @14
    @1
    @17
    @0
    @14
    @1
    @15
    adantr
    @0
    @1
    simpr
    @8
    @1
    vs
    cX
    cC
    @4
    cX
    cU
    sseq2
    elrab
    sylanbrc
    @9
    cX
    ne0i
    syl
    @9
    intex
    sylib
    fvmptd
end
