include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "cec.mm"
include "cdm.mm"
include "wrex.mm"
include "wb.mm"
include "cres.mm"
include "resdm.mm"
include "cosseqd.mm"
include "breqd.mm"
include "adantl.mm"
include "br1cossres2.mm"
include "adantr.mm"
include "bitr3d.mm"
include "ex.mm"

theorem relbrcoss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint V x
  disjoint W x
  assert |- ( ( A e. V /\ B e. W ) -> ( Rel R -> ( A ,~ R B <-> E. x e. dom R ( A e. [ x ] R /\ B e. [ x ] R ) ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cR
    wrel
    #
    cA
    cB
    cR
    ccoss
    #
    wbr
    #
    cA
    vx
    cv
    cR
    cec
    #
    wcel
    cB
    @4
    wcel
    wa
    vx
    cR
    cdm
    #
    wrex
    #
    wb
    @0
    @1
    wa
    cA
    cB
    cR
    @5
    cres
    #
    ccoss
    #
    wbr
    #
    @3
    @6
    @1
    @9
    @3
    wb
    @0
    @1
    @8
    @2
    cA
    cB
    @1
    @7
    cR
    cR
    resdm
    cosseqd
    breqd
    adantl
    @0
    @9
    @6
    wb
    @1
    vx
    @5
    cA
    cB
    cR
    cV
    cW
    br1cossres2
    adantr
    bitr3d
    ex
end
