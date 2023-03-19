include "co.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wbr.mm"
include "wrel.mm"
include "homarel.mm"
include "1st2ndbr.mm"
include "mpan.mm"
include "homahom2.mm"
include "syl.mm"

theorem homahom
  let cC: class C
  let cF: class F
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )
  assume homahom.j: |- J = ( Hom ` C )


  assert |- ( F e. ( X H Y ) -> ( 2nd ` F ) e. ( X J Y ) )

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
    c1st
    cfv
    #
    cF
    c2nd
    cfv
    #
    @0
    wbr
    #
    @3
    cX
    cY
    cJ
    co
    wcel
    @0
    wrel
    @1
    @4
    cC
    cH
    cX
    cY
    homahom.h
    homarel
    cF
    @0
    1st2ndbr
    mpan
    cC
    @3
    cH
    cJ
    cX
    cY
    @2
    homahom.h
    homahom.j
    homahom2
    syl
end
