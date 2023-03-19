include "co.mm"
include "cv.mm"
include "cfv.mm"
include "c2nd.mm"
include "c1st.mm"
include "cop.mm"
include "cvv.mm"
include "evlf2.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "fveq1d.mm"
include "simprr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem evlf2val
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let ve: setvar e
  let vz: setvar z
  assume evlfval.e: |- E = ( C evalF D )
  assume evlfval.c: |- ( ph -> C e. Cat )
  assume evlfval.d: |- ( ph -> D e. Cat )
  assume evlfval.b: |- B = ( Base ` C )
  assume evlfval.h: |- H = ( Hom ` C )
  assume evlfval.o: |- .x. = ( comp ` D )
  assume evlfval.n: |- N = ( C Nat D )
  assume evlf2.f: |- ( ph -> F e. ( C Func D ) )
  assume evlf2.g: |- ( ph -> G e. ( C Func D ) )
  assume evlf2.x: |- ( ph -> X e. B )
  assume evlf2.y: |- ( ph -> Y e. B )
  assume evlf2.l: |- L = ( <. F , X >. ( 2nd ` E ) <. G , Y >. )
  assume evlf2val.a: |- ( ph -> A e. ( F N G ) )
  assume evlf2val.k: |- ( ph -> K e. ( X H Y ) )


  assert |- ( ph -> ( A L K ) = ( ( A ` Y ) ( <. ( ( 1st ` F ) ` X ) , ( ( 1st ` F ) ` Y ) >. .x. ( ( 1st ` G ) ` Y ) ) ( ( X ( 2nd ` F ) Y ) ` K ) ) )

  proof
    wph
    va
    vg
    cA
    cK
    cF
    cG
    cN
    co
    cX
    cY
    cH
    co
    cY
    va
    cv
    #
    cfv
    #
    vg
    cv
    #
    cX
    cY
    cF
    c2nd
    cfv
    co
    #
    cfv
    #
    cX
    cF
    c1st
    cfv
    #
    cfv
    cY
    @5
    cfv
    cop
    cY
    cG
    c1st
    cfv
    cfv
    c.x
    co
    #
    co
    cY
    cA
    cfv
    #
    cK
    @3
    cfv
    #
    @6
    co
    cL
    cvv
    wph
    cB
    cC
    cD
    c.x
    vg
    cE
    cF
    cG
    cH
    cL
    cN
    cX
    cY
    va
    evlfval.e
    evlfval.c
    evlfval.d
    evlfval.b
    evlfval.h
    evlfval.o
    evlfval.n
    evlf2.f
    evlf2.g
    evlf2.x
    evlf2.y
    evlf2.l
    evlf2
    wph
    @0
    cA
    wceq
    #
    @2
    cK
    wceq
    #
    wa
    wa
    #
    @1
    @7
    @4
    @8
    @6
    @11
    cY
    @0
    cA
    wph
    @9
    @10
    simprl
    fveq1d
    @11
    @2
    cK
    @3
    wph
    @9
    @10
    simprr
    fveq2d
    oveq12d
    evlf2val.a
    evlf2val.k
    wph
    @7
    @8
    @6
    ovexd
    ovmpt2d
end
