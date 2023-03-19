include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "c1st.mm"
include "cc.mm"
include "cop.mm"
include "cv.mm"
include "opeq1.mm"
include "df-bj-inftyexpi.mm"
include "opex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "cnex.mm"
include "op1stg.mm"
include "mpan2.mm"
include "eqtrd.mm"

theorem bj-inftyexpiinv
  let cA: class A
  let vx: setvar x


  assert |- ( A e. ( -u _pi (,] _pi ) -> ( 1st ` ( inftyexpi ` A ) ) = A )

  proof
    cA
    cpi
    cneg
    cpi
    cioc
    co
    #
    wcel
    #
    cA
    cinftyexpi
    cfv
    #
    c1st
    cfv
    cA
    cc
    cop
    #
    c1st
    cfv
    #
    cA
    @1
    @2
    @3
    c1st
    vx
    cA
    vx
    cv
    #
    cc
    cop
    @3
    @0
    cinftyexpi
    @5
    cA
    cc
    opeq1
    vx
    df-bj-inftyexpi
    cA
    cc
    opex
    fvmpt
    fveq2d
    @1
    cc
    cvv
    wcel
    @4
    cA
    wceq
    cnex
    cA
    cc
    @0
    cvv
    op1stg
    mpan2
    eqtrd
end
