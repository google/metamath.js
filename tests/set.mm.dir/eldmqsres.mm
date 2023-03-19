include "wcel.mm"
include "cres.mm"
include "cdm.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "wex.mm"
include "wa.mm"
include "elqsg.mm"
include "wb.mm"
include "cvv.mm"
include "eldmres2.mm"
include "elv.mm"
include "anbi1i.mm"
include "ecres2.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "anbi2i.mm"
include "w3a.mm"
include "3ancoma.mm"
include "df-3an.mm"
include "3anass.mm"
include "3bitr3i.mm"
include "an12.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "rexbii2.mm"
include "syl6bb.mm"

theorem eldmqsres
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint B u
  disjoint R u
  disjoint R x
  assert |- ( B e. V -> ( B e. ( dom ( R |` A ) /. ( R |` A ) ) <-> E. u e. A ( E. x x e. [ u ] R /\ B = [ u ] R ) ) )

  proof
    cB
    cV
    wcel
    cB
    cR
    cA
    cres
    #
    cdm
    #
    @0
    cqs
    wcel
    cB
    vu
    cv
    #
    @0
    cec
    #
    wceq
    #
    vu
    @1
    wrex
    vx
    cv
    @2
    cR
    cec
    #
    wcel
    vx
    wex
    #
    cB
    @5
    wceq
    #
    wa
    #
    vu
    cA
    wrex
    vu
    @1
    cB
    @0
    cV
    elqsg
    @4
    @8
    vu
    @1
    cA
    @2
    @1
    wcel
    #
    @4
    wa
    @2
    cA
    wcel
    #
    @6
    wa
    #
    @4
    wa
    #
    @10
    @8
    wa
    #
    @9
    @11
    @4
    @9
    @11
    wb
    vu
    vx
    cA
    @2
    cR
    cvv
    eldmres2
    elv
    anbi1i
    @6
    @10
    @4
    wa
    #
    wa
    #
    @6
    @10
    @7
    wa
    #
    wa
    @12
    @13
    @14
    @16
    @6
    @10
    @4
    @7
    @10
    @3
    @5
    cB
    cA
    @2
    cR
    ecres2
    eqeq2d
    pm5.32i
    anbi2i
    @10
    @6
    @4
    w3a
    @6
    @10
    @4
    w3a
    @12
    @15
    @10
    @6
    @4
    3ancoma
    @10
    @6
    @4
    df-3an
    @6
    @10
    @4
    3anass
    3bitr3i
    @10
    @6
    @7
    an12
    3bitr4i
    bitri
    rexbii2
    syl6bb
end
