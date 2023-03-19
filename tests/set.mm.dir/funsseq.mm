include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "w3a.mm"
include "wss.mm"
include "eqimss.mm"
include "wa.mm"
include "cres.mm"
include "simpl3.mm"
include "reseq2d.mm"
include "funssres.mm"
include "3ad2antl2.mm"
include "wrel.mm"
include "simpl2.mm"
include "funrel.mm"
include "resdm.mm"
include "3syl.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "impbid2.mm"

theorem funsseq
  let cF: class F
  let cG: class G


  assert |- ( ( Fun F /\ Fun G /\ dom F = dom G ) -> ( F = G <-> F C_ G ) )

  proof
    cF
    wfun
    #
    cG
    wfun
    #
    cF
    cdm
    #
    cG
    cdm
    #
    wceq
    #
    w3a
    #
    cF
    cG
    wceq
    #
    cF
    cG
    wss
    #
    cF
    cG
    eqimss
    @5
    @7
    @6
    @5
    @7
    wa
    #
    cG
    @2
    cres
    #
    cG
    @3
    cres
    #
    cF
    cG
    @8
    @2
    @3
    cG
    @0
    @1
    @4
    @7
    simpl3
    reseq2d
    @1
    @0
    @7
    @9
    cF
    wceq
    @4
    cG
    cF
    funssres
    3ad2antl2
    @8
    @1
    cG
    wrel
    @10
    cG
    wceq
    @0
    @1
    @4
    @7
    simpl2
    cG
    funrel
    cG
    resdm
    3syl
    3eqtr3d
    ex
    impbid2
end
