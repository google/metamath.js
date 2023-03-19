include "wf.mm"
include "cin.mm"
include "cres.mm"
include "cdm.mm"
include "fdm.mm"
include "eqcomd.mm"
include "ineq2d.mm"
include "reseq2d.mm"
include "wrel.mm"
include "wceq.mm"
include "frel.mm"
include "resindm.mm"
include "syl.mm"
include "eqtrd.mm"

theorem fresin2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( F : A --> B -> ( F |` ( C i^i A ) ) = ( F |` C ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cC
    cA
    cin
    #
    cres
    cF
    cC
    cF
    cdm
    #
    cin
    #
    cres
    #
    cF
    cC
    cres
    #
    @0
    @1
    @3
    cF
    @0
    cA
    @2
    cC
    @0
    @2
    cA
    cA
    cB
    cF
    fdm
    eqcomd
    ineq2d
    reseq2d
    @0
    cF
    wrel
    @4
    @5
    wceq
    cA
    cB
    cF
    frel
    cF
    cC
    resindm
    syl
    eqtrd
end
