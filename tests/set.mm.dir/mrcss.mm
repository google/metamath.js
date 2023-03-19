include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "sstr2.mm"
include "adantr.mm"
include "ss2rabdv.mm"
include "intss.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "wceq.mm"
include "simp1.mm"
include "sstr.mm"
include "3adant1.mm"
include "mrcval.mm"
include "syl2anc.mm"
include "3adant2.mm"
include "3sstr4d.mm"

theorem mrcss
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ V /\ V C_ X ) -> ( F ` U ) C_ ( F ` V ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cV
    wss
    #
    cV
    cX
    wss
    #
    w3a
    #
    cU
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
    cV
    @4
    wss
    #
    vs
    cC
    crab
    #
    cint
    #
    cU
    cF
    cfv
    #
    cV
    cF
    cfv
    #
    @1
    @0
    @7
    @10
    wss
    #
    @2
    @1
    @9
    @6
    wss
    @13
    @1
    @8
    @5
    vs
    cC
    @1
    @8
    @5
    wi
    @4
    cC
    wcel
    cU
    cV
    @4
    sstr2
    adantr
    ss2rabdv
    @9
    @6
    intss
    syl
    3ad2ant2
    @3
    @0
    cU
    cX
    wss
    #
    @11
    @7
    wceq
    @0
    @1
    @2
    simp1
    @1
    @2
    @14
    @0
    cU
    cV
    cX
    sstr
    3adant1
    cC
    cU
    cF
    cX
    vs
    mrcfval.f
    mrcval
    syl2anc
    @0
    @2
    @12
    @10
    wceq
    @1
    cC
    cV
    cF
    cX
    vs
    mrcfval.f
    mrcval
    3adant2
    3sstr4d
end
