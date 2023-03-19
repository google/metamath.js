include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cotp.mm"
include "wceq.mm"
include "mpstssv.mm"
include "sseli.mm"
include "cop.mm"
include "1st2nd2.mm"
include "xp1st.mm"
include "syl.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "df-ot.mm"
include "syl6eqr.mm"

theorem mpst123
  let cP: class P
  let cT: class T
  let cX: class X
  let va: setvar a
  let vh: setvar h
  let vs: setvar s
  let vz: setvar z
  let cR: class R
  let vd: setvar d
  assume mpstssv.p: |- P = ( mPreSt ` T )


  assert |- ( X e. P -> X = <. ( 1st ` ( 1st ` X ) ) , ( 2nd ` ( 1st ` X ) ) , ( 2nd ` X ) >. )

  proof
    cX
    cP
    wcel
    cX
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    wcel
    #
    cX
    cX
    c1st
    cfv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cX
    c2nd
    cfv
    #
    cotp
    #
    wceq
    cP
    @1
    cX
    cP
    cT
    mpstssv.p
    mpstssv
    sseli
    @2
    cX
    @4
    @5
    cop
    #
    @6
    cop
    #
    @7
    @2
    cX
    @3
    @6
    cop
    @9
    cX
    @0
    cvv
    1st2nd2
    @2
    @3
    @8
    @6
    @2
    @3
    @0
    wcel
    @3
    @8
    wceq
    cX
    @0
    cvv
    xp1st
    @3
    cvv
    cvv
    1st2nd2
    syl
    opeq1d
    eqtrd
    @4
    @5
    @6
    df-ot
    syl6eqr
    syl
end
