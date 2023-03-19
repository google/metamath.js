include "cxp.mm"
include "wf.mm"
include "c2nd.mm"
include "ccom.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "cvv.mm"
include "wfo.mm"
include "fo2nd.mm"
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
include "f2ndres.mm"
include "syl6ss.mm"
include "syl5eqss.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem 2ndcof
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( F : A --> ( B X. C ) -> ( 2nd o. F ) : A --> C )

  proof
    cA
    cB
    cC
    cxp
    #
    cF
    wf
    #
    c2nd
    cF
    ccom
    #
    cA
    wfn
    #
    @2
    crn
    #
    cC
    wss
    cA
    cC
    @2
    wf
    @1
    c2nd
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
    c2nd
    wfo
    @5
    fo2nd
    cvv
    cvv
    c2nd
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
    c2nd
    cF
    fnfco
    sylancr
    @1
    @4
    c2nd
    cF
    crn
    #
    cres
    #
    crn
    #
    cC
    c2nd
    cF
    rnco
    @1
    @9
    c2nd
    @0
    cres
    #
    crn
    #
    cC
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
    c2nd
    ssres2
    @8
    @10
    rnss
    3syl
    @0
    cC
    @10
    wf
    @11
    cC
    wss
    cB
    cC
    f2ndres
    @0
    cC
    @10
    frn
    ax-mp
    syl6ss
    syl5eqss
    cA
    cC
    @2
    df-f
    sylanbrc
end
