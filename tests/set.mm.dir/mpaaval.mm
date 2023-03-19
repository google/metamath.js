include "cv.mm"
include "cdgr.mm"
include "cfv.mm"
include "cdgraa.mm"
include "wceq.mm"
include "cc0.mm"
include "ccoe.mm"
include "c1.mm"
include "w3a.mm"
include "cq.mm"
include "cply.mm"
include "crio.mm"
include "caa.mm"
include "cmpaa.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "3anbi123d.mm"
include "riotabidv.mm"
include "df-mpaa.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem mpaaval
  let cA: class A
  let vp: setvar p
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P

  disjoint A p
  disjoint A d
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d p
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint P d
  disjoint P p
  disjoint P a
  disjoint P b
  disjoint P c
  assert |- ( A e. AA -> ( minPolyAA ` A ) = ( iota_ p e. ( Poly ` QQ ) ( ( deg ` p ) = ( degAA ` A ) /\ ( p ` A ) = 0 /\ ( ( coeff ` p ) ` ( degAA ` A ) ) = 1 ) ) )

  proof
    va
    cA
    vp
    cv
    #
    cdgr
    cfv
    #
    va
    cv
    #
    cdgraa
    cfv
    #
    wceq
    #
    @2
    @0
    cfv
    #
    cc0
    wceq
    #
    @3
    @0
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    w3a
    #
    vp
    cq
    cply
    cfv
    #
    crio
    @1
    cA
    cdgraa
    cfv
    #
    wceq
    #
    cA
    @0
    cfv
    #
    cc0
    wceq
    #
    @12
    @7
    cfv
    #
    c1
    wceq
    #
    w3a
    #
    vp
    @11
    crio
    caa
    cmpaa
    @2
    cA
    wceq
    #
    @10
    @18
    vp
    @11
    @19
    @4
    @13
    @6
    @15
    @9
    @17
    @19
    @3
    @12
    @1
    @2
    cA
    cdgraa
    fveq2
    #
    eqeq2d
    @19
    @5
    @14
    cc0
    @2
    cA
    @0
    fveq2
    eqeq1d
    @19
    @8
    @16
    c1
    @19
    @3
    @12
    @7
    @20
    fveq2d
    eqeq1d
    3anbi123d
    riotabidv
    va
    vp
    df-mpaa
    @18
    vp
    @11
    riotaex
    fvmpt
end
