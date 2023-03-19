include "cfunc.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cnat.mm"
include "c2nd.mm"
include "chom.mm"
include "cop.mm"
include "cco.mm"
include "csb.mm"
include "wceq.mm"
include "eqid.mm"
include "evlfval.mm"
include "ovex.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "xpex.mm"
include "op1std.mm"
include "syl.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "simprr.mm"
include "fveq12d.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem evlf1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  assume evlf1.e: |- E = ( C evalF D )
  assume evlf1.c: |- ( ph -> C e. Cat )
  assume evlf1.d: |- ( ph -> D e. Cat )
  assume evlf1.b: |- B = ( Base ` C )
  assume evlf1.f: |- ( ph -> F e. ( C Func D ) )
  assume evlf1.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( F ( 1st ` E ) X ) = ( ( 1st ` F ) ` X ) )

  proof
    wph
    vf
    vx
    cF
    cX
    cC
    cD
    cfunc
    co
    #
    cB
    vx
    cv
    #
    vf
    cv
    #
    c1st
    cfv
    #
    cfv
    #
    cX
    cF
    c1st
    cfv
    #
    cfv
    cE
    c1st
    cfv
    #
    cvv
    wph
    cE
    vf
    vx
    @0
    cB
    @4
    cmpt2
    #
    vx
    vy
    @0
    cB
    cxp
    #
    @8
    vm
    @1
    c1st
    cfv
    vn
    vy
    cv
    #
    c1st
    cfv
    va
    vg
    vm
    cv
    #
    vn
    cv
    #
    cC
    cD
    cnat
    co
    #
    co
    @1
    c2nd
    cfv
    #
    @9
    c2nd
    cfv
    #
    cC
    chom
    cfv
    #
    co
    @14
    va
    cv
    cfv
    vg
    cv
    @13
    @14
    @10
    c2nd
    cfv
    co
    cfv
    @13
    @10
    c1st
    cfv
    #
    cfv
    @14
    @16
    cfv
    cop
    @14
    @11
    c1st
    cfv
    cfv
    cD
    cco
    cfv
    #
    co
    co
    cmpt2
    csb
    csb
    #
    cmpt2
    #
    cop
    wceq
    @6
    @7
    wceq
    wph
    vx
    vy
    cB
    cC
    cD
    @17
    vf
    vg
    vm
    vn
    cE
    @15
    @12
    va
    evlf1.e
    evlf1.c
    evlf1.d
    evlf1.b
    @15
    eqid
    @17
    eqid
    @12
    eqid
    evlfval
    @7
    @19
    cE
    vf
    vx
    @0
    cB
    @4
    cC
    cD
    cfunc
    ovex
    #
    cB
    cC
    cbs
    cfv
    cvv
    evlf1.b
    cC
    cbs
    fvex
    eqeltri
    #
    mpt2ex
    vx
    vy
    @8
    @8
    @18
    @0
    cB
    @20
    @21
    xpex
    #
    @22
    mpt2ex
    op1std
    syl
    wph
    @2
    cF
    wceq
    #
    @1
    cX
    wceq
    #
    wa
    wa
    #
    @1
    cX
    @3
    @5
    @25
    @2
    cF
    c1st
    wph
    @23
    @24
    simprl
    fveq2d
    wph
    @23
    @24
    simprr
    fveq12d
    evlf1.f
    evlf1.x
    wph
    cX
    @5
    fvexd
    ovmpt2d
end
