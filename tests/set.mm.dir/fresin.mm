include "wf.mm"
include "cin.mm"
include "cres.mm"
include "wss.mm"
include "inss1.mm"
include "fssres.mm"
include "mpan2.mm"
include "resres.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnresdm.mm"
include "syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"

theorem fresin
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X


  assert |- ( F : A --> B -> ( F |` X ) : ( A i^i X ) --> B )

  proof
    cA
    cB
    cF
    wf
    #
    cA
    cX
    cin
    #
    cB
    cF
    @1
    cres
    #
    wf
    #
    @1
    cB
    cF
    cX
    cres
    #
    wf
    @0
    @1
    cA
    wss
    @3
    cA
    cX
    inss1
    cA
    cB
    @1
    cF
    fssres
    mpan2
    @0
    @1
    cB
    @2
    @4
    @0
    @2
    cF
    cA
    cres
    #
    cX
    cres
    @4
    cF
    cA
    cX
    resres
    @0
    @5
    cF
    cX
    @0
    cF
    cA
    wfn
    @5
    cF
    wceq
    cA
    cB
    cF
    ffn
    cA
    cF
    fnresdm
    syl
    reseq1d
    syl5eqr
    feq1d
    mpbid
end
