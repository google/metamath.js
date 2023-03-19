include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "cfunc.mm"
include "co.mm"
include "cvv.mm"
include "ccid.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "fuccatid.mm"
include "syl5eq.mm"
include "simpr.mm"
include "fveq2d.mm"
include "coeq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "coex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem fucid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let c.1: class .1.
  let cF: class F
  let cI: class I
  let vf: setvar f
  assume fucid.q: |- Q = ( C FuncCat D )
  assume fucid.i: |- I = ( Id ` Q )
  assume fucid.1: |- .1. = ( Id ` D )
  assume fucid.f: |- ( ph -> F e. ( C Func D ) )


  assert |- ( ph -> ( I ` F ) = ( .1. o. ( 1st ` F ) ) )

  proof
    wph
    vf
    cF
    c.1
    vf
    cv
    #
    c1st
    cfv
    #
    ccom
    #
    c.1
    cF
    c1st
    cfv
    #
    ccom
    #
    cC
    cD
    cfunc
    co
    #
    cI
    cvv
    wph
    cI
    cQ
    ccid
    cfv
    #
    vf
    @5
    @2
    cmpt
    #
    fucid.i
    wph
    cQ
    ccat
    wcel
    @6
    @7
    wceq
    wph
    cC
    cD
    cQ
    c.1
    vf
    fucid.q
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    wph
    cF
    @5
    wcel
    @8
    @9
    wa
    fucid.f
    cC
    cD
    cF
    funcrcl
    syl
    #
    simpld
    wph
    @8
    @9
    @10
    simprd
    fucid.1
    fuccatid
    simprd
    syl5eq
    wph
    @0
    cF
    wceq
    #
    wa
    #
    @1
    @3
    c.1
    @12
    @0
    cF
    c1st
    wph
    @11
    simpr
    fveq2d
    coeq2d
    fucid.f
    @4
    cvv
    wcel
    wph
    c.1
    @3
    c.1
    cD
    ccid
    cfv
    cvv
    fucid.1
    cD
    ccid
    fvex
    eqeltri
    cF
    c1st
    fvex
    coex
    a1i
    fvmptd
end
