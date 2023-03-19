include "cun.mm"
include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cres.mm"
include "reseq1.mm"
include "jca.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "fveq1.mm"
include "fvres.mm"
include "sylan9req.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "adantlr.mm"
include "adantll.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "eqfnfv.mm"
include "syl5ibr.mm"
include "impbid2.mm"

theorem eqfnun
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vx: setvar x


  assert |- ( ( F Fn ( A u. B ) /\ G Fn ( A u. B ) ) -> ( F = G <-> ( ( F |` A ) = ( G |` A ) /\ ( F |` B ) = ( G |` B ) ) ) )

  proof
    cF
    cA
    cB
    cun
    #
    wfn
    cG
    @0
    wfn
    wa
    #
    cF
    cG
    wceq
    #
    cF
    cA
    cres
    #
    cG
    cA
    cres
    #
    wceq
    #
    cF
    cB
    cres
    #
    cG
    cB
    cres
    #
    wceq
    #
    wa
    #
    @2
    @5
    @8
    cF
    cG
    cA
    reseq1
    cF
    cG
    cB
    reseq1
    jca
    @9
    @2
    @1
    vx
    cv
    #
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    wceq
    #
    vx
    @0
    wral
    @9
    @13
    vx
    @0
    @10
    @0
    wcel
    @9
    @10
    cA
    wcel
    #
    @10
    cB
    wcel
    #
    wo
    @13
    @10
    cA
    cB
    elun
    @9
    @14
    @13
    @15
    @5
    @14
    @13
    @8
    @5
    @14
    wa
    @10
    @4
    cfv
    #
    @11
    @12
    @5
    @14
    @16
    @10
    @3
    cfv
    @11
    @10
    @3
    @4
    fveq1
    @10
    cA
    cF
    fvres
    sylan9req
    @14
    @16
    @12
    wceq
    @5
    @10
    cA
    cG
    fvres
    adantl
    eqtr3d
    adantlr
    @8
    @15
    @13
    @5
    @8
    @15
    wa
    @10
    @7
    cfv
    #
    @11
    @12
    @8
    @15
    @17
    @10
    @6
    cfv
    @11
    @10
    @6
    @7
    fveq1
    @10
    cB
    cF
    fvres
    sylan9req
    @15
    @17
    @12
    wceq
    @8
    @10
    cB
    cG
    fvres
    adantl
    eqtr3d
    adantll
    jaodan
    sylan2b
    ralrimiva
    vx
    @0
    cF
    cG
    eqfnfv
    syl5ibr
    impbid2
end
