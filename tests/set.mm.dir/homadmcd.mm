include "co.mm"
include "wcel.mm"
include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "cotp.mm"
include "c1st.mm"
include "wrel.mm"
include "wceq.mm"
include "homarel.mm"
include "1st2nd.mm"
include "mpan.mm"
include "wbr.mm"
include "1st2ndbr.mm"
include "homa1.mm"
include "syl.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "df-ot.mm"
include "syl6eqr.mm"

theorem homadmcd
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )


  assert |- ( F e. ( X H Y ) -> F = <. X , Y , ( 2nd ` F ) >. )

  proof
    cF
    cX
    cY
    cH
    co
    #
    wcel
    #
    cF
    cX
    cY
    cop
    #
    cF
    c2nd
    cfv
    #
    cop
    #
    cX
    cY
    @3
    cotp
    @1
    cF
    cF
    c1st
    cfv
    #
    @3
    cop
    #
    @4
    @0
    wrel
    #
    @1
    cF
    @6
    wceq
    cC
    cH
    cX
    cY
    homahom.h
    homarel
    #
    cF
    @0
    1st2nd
    mpan
    @1
    @5
    @2
    @3
    @1
    @5
    @3
    @0
    wbr
    #
    @5
    @2
    wceq
    @7
    @1
    @9
    @8
    cF
    @0
    1st2ndbr
    mpan
    cC
    @3
    cH
    cX
    cY
    @5
    homahom.h
    homa1
    syl
    opeq1d
    eqtrd
    cX
    cY
    @3
    df-ot
    syl6eqr
end
