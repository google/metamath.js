include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "cpjh.mm"
include "wceq.mm"
include "cv.mm"
include "cva.mm"
include "wrex.mm"
include "wa.mm"
include "wb.mm"
include "pjhth.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "pjpreeq.mm"
include "syldan.mm"

theorem pjeq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cH: class H
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z

  disjoint H x
  disjoint A x
  disjoint B x
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint H h
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( ( projh ` H ) ` A ) = B <-> ( B e. H /\ E. x e. ( _|_ ` H ) A = ( B +h x ) ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cH
    cH
    cort
    cfv
    #
    cph
    co
    #
    wcel
    #
    cA
    cH
    cpjh
    cfv
    cfv
    cB
    wceq
    cB
    cH
    wcel
    cA
    cB
    vx
    cv
    cva
    co
    wceq
    vx
    @2
    wrex
    wa
    wb
    @0
    @4
    @1
    @0
    @3
    chil
    cA
    cH
    pjhth
    eleq2d
    biimpar
    vx
    cA
    cB
    cH
    pjpreeq
    syldan
end
