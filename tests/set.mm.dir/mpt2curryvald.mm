include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "ccur.mm"
include "cvv.mm"
include "mpt2curryd.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfmpt.mm"
include "weq.mm"
include "csbeq1a.mm"
include "mpteq2dv.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "wceq.mm"
include "wa.mm"
include "csbeq1.mm"
include "adantl.mm"
include "wcel.mm"
include "mptexg.mm"
include "syl.mm"
include "fvmptd.mm"

theorem mpt2curryvald
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  assume mpt2curryd.f: |- F = ( x e. X , y e. Y |-> C )
  assume mpt2curryd.c: |- ( ph -> A. x e. X A. y e. Y C e. V )
  assume mpt2curryd.n: |- ( ph -> Y =/= (/) )
  assume mpt2curryvald.y: |- ( ph -> Y e. W )
  assume mpt2curryvald.a: |- ( ph -> A e. X )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint A x
  disjoint A y
  disjoint C a
  disjoint C b
  disjoint a b
  disjoint C z
  disjoint F z
  disjoint x z
  disjoint y z
  disjoint V z
  disjoint X a
  disjoint X b
  disjoint X z
  disjoint Y a
  disjoint Y b
  disjoint Y z
  disjoint a ph
  disjoint b ph
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint ph z
  disjoint A a
  assert |- ( ph -> ( curry F ` A ) = ( y e. Y |-> [_ A / x ]_ C ) )

  proof
    wph
    va
    cA
    vy
    cY
    vx
    va
    cv
    #
    cC
    csb
    #
    cmpt
    #
    vy
    cY
    vx
    cA
    cC
    csb
    #
    cmpt
    #
    cX
    cF
    ccur
    #
    cvv
    wph
    @5
    vx
    cX
    vy
    cY
    cC
    cmpt
    #
    cmpt
    va
    cX
    @2
    cmpt
    wph
    vx
    vy
    cC
    cF
    cV
    cX
    cY
    mpt2curryd.f
    mpt2curryd.c
    mpt2curryd.n
    mpt2curryd
    vx
    va
    cX
    @6
    @2
    va
    @6
    nfcv
    vx
    vy
    cY
    @1
    vx
    cY
    nfcv
    vx
    @0
    cC
    nfcsb1v
    nfmpt
    vx
    va
    weq
    vy
    cY
    cC
    @1
    vx
    @0
    cC
    csbeq1a
    mpteq2dv
    cbvmpt
    syl6eq
    wph
    @0
    cA
    wceq
    #
    wa
    vy
    cY
    @1
    @3
    @7
    @1
    @3
    wceq
    wph
    vx
    @0
    cA
    cC
    csbeq1
    adantl
    mpteq2dv
    mpt2curryvald.a
    wph
    cY
    cW
    wcel
    @4
    cvv
    wcel
    mpt2curryvald.y
    vy
    cY
    @3
    cW
    mptexg
    syl
    fvmptd
end
