include "cxp.mm"
include "wf.mm"
include "c1st.mm"
include "ccom.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "cvv.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ffn.mm"
include "dffn2.mm"
include "sylib.mm"
include "fnfco.mm"
include "sylancr.mm"
include "cres.mm"
include "rnco.mm"
include "frn.mm"
include "ssres2.mm"
include "rnss.mm"
include "3syl.mm"
include "f1stres.mm"
include "syl6ss.mm"
include "syl5eqss.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem 1stcof
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( F : A --> ( B X. C ) -> ( 1st o. F ) : A --> B )

  proof
    cA
    cB
    cC
    cxp
    #
    cF
    wf
    #
    c1st
    cF
    ccom
    #
    cA
    wfn
    #
    @2
    crn
    #
    cB
    wss
    cA
    cB
    @2
    wf
    @1
    c1st
    cvv
    wfn
    #
    cA
    cvv
    cF
    wf
    #
    @3
    cvv
    cvv
    c1st
    wfo
    @5
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @1
    cF
    cA
    wfn
    @6
    cA
    @0
    cF
    ffn
    cA
    cF
    dffn2
    sylib
    cvv
    cA
    c1st
    cF
    fnfco
    sylancr
    @1
    @4
    c1st
    cF
    crn
    #
    cres
    #
    crn
    #
    cB
    c1st
    cF
    rnco
    @1
    @9
    c1st
    @0
    cres
    #
    crn
    #
    cB
    @1
    @7
    @0
    wss
    @8
    @10
    wss
    @9
    @11
    wss
    cA
    @0
    cF
    frn
    @7
    @0
    c1st
    ssres2
    @8
    @10
    rnss
    3syl
    @0
    cB
    @10
    wf
    @11
    cB
    wss
    cB
    cC
    f1stres
    @0
    cB
    @10
    frn
    ax-mp
    syl6ss
    syl5eqss
    cA
    cB
    @2
    df-f
    sylanbrc
end
