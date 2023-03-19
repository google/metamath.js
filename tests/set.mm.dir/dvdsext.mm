include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "breq1.mm"
include "ralrimivw.mm"
include "simpll.mm"
include "simplr.mm"
include "cz.mm"
include "nn0z.mm"
include "iddvds.mm"
include "syl.mm"
include "ad2antlr.mm"
include "breq2.mm"
include "bibi12d.mm"
include "rspcva.mm"
include "adantll.mm"
include "mpbird.mm"
include "ad2antrr.mm"
include "adantlr.mm"
include "mpbid.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "ex.mm"
include "impbid2.mm"

theorem dvdsext
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N

  disjoint A x
  disjoint B x
  disjoint N x
  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A = B <-> A. x e. NN0 ( A || x <-> B || x ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    cA
    vx
    cv
    #
    cdvds
    wbr
    #
    cB
    @4
    cdvds
    wbr
    #
    wb
    #
    vx
    cn0
    wral
    #
    @3
    @7
    vx
    cn0
    cA
    cB
    @4
    cdvds
    breq1
    ralrimivw
    @2
    @8
    @3
    @2
    @8
    wa
    #
    @0
    @1
    cA
    cB
    cdvds
    wbr
    #
    cB
    cA
    cdvds
    wbr
    #
    @3
    @0
    @1
    @8
    simpll
    @0
    @1
    @8
    simplr
    @9
    @10
    cB
    cB
    cdvds
    wbr
    #
    @1
    @12
    @0
    @8
    @1
    cB
    cz
    wcel
    @12
    cB
    nn0z
    cB
    iddvds
    syl
    ad2antlr
    @1
    @8
    @10
    @12
    wb
    #
    @0
    @7
    @13
    vx
    cB
    cn0
    @4
    cB
    wceq
    @5
    @10
    @6
    @12
    @4
    cB
    cA
    cdvds
    breq2
    @4
    cB
    cB
    cdvds
    breq2
    bibi12d
    rspcva
    adantll
    mpbird
    @9
    cA
    cA
    cdvds
    wbr
    #
    @11
    @0
    @14
    @1
    @8
    @0
    cA
    cz
    wcel
    @14
    cA
    nn0z
    cA
    iddvds
    syl
    ad2antrr
    @0
    @8
    @14
    @11
    wb
    #
    @1
    @7
    @15
    vx
    cA
    cn0
    @4
    cA
    wceq
    @5
    @14
    @6
    @11
    @4
    cA
    cA
    cdvds
    breq2
    @4
    cA
    cB
    cdvds
    breq2
    bibi12d
    rspcva
    adantlr
    mpbid
    cA
    cB
    dvdseq
    syl22anc
    ex
    impbid2
end
