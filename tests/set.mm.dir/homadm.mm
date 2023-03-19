include "co.mm"
include "wcel.mm"
include "cdoma.mm"
include "cfv.mm"
include "c1st.mm"
include "cop.mm"
include "ccom.mm"
include "df-doma.mm"
include "fveq1i.mm"
include "cvv.mm"
include "wf.mm"
include "wceq.mm"
include "wfo.mm"
include "fo1st.mm"
include "fof.mm"
include "ax-mp.mm"
include "elex.mm"
include "fvco3.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "c2nd.mm"
include "wbr.mm"
include "wrel.mm"
include "homarel.mm"
include "1st2ndbr.mm"
include "mpan.mm"
include "homa1.mm"
include "syl.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wa.mm"
include "eqid.mm"
include "homarcl2.mm"
include "op1stg.mm"
include "3eqtrd.mm"

theorem homadm
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )


  assert |- ( F e. ( X H Y ) -> ( domA ` F ) = X )

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
    cdoma
    cfv
    #
    cF
    c1st
    cfv
    #
    c1st
    cfv
    #
    cX
    cY
    cop
    #
    c1st
    cfv
    #
    cX
    @1
    @2
    cF
    c1st
    c1st
    ccom
    #
    cfv
    #
    @4
    cF
    cdoma
    @7
    df-doma
    fveq1i
    @1
    cvv
    cvv
    c1st
    wf
    #
    cF
    cvv
    wcel
    @8
    @4
    wceq
    cvv
    cvv
    c1st
    wfo
    @9
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    cF
    @0
    elex
    cvv
    cvv
    cF
    c1st
    c1st
    fvco3
    sylancr
    syl5eq
    @1
    @3
    @5
    c1st
    @1
    @3
    cF
    c2nd
    cfv
    #
    @0
    wbr
    #
    @3
    @5
    wceq
    @0
    wrel
    @1
    @11
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
    @10
    cH
    cX
    cY
    @3
    homahom.h
    homa1
    syl
    fveq2d
    @1
    cX
    cC
    cbs
    cfv
    #
    wcel
    cY
    @12
    wcel
    wa
    @6
    cX
    wceq
    @12
    cC
    cF
    cH
    cX
    cY
    homahom.h
    @12
    eqid
    homarcl2
    cX
    cY
    @12
    @12
    op1stg
    syl
    3eqtrd
end
