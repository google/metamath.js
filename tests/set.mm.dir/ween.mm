include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wwe.mm"
include "wex.mm"
include "dfac8b.mm"
include "cvv.mm"
include "cpw.mm"
include "cuni.mm"
include "wor.mm"
include "weso.mm"
include "vex.mm"
include "soex.mm"
include "sylancl.mm"
include "exlimiv.mm"
include "wceq.mm"
include "wb.mm"
include "unipw.mm"
include "weeq2.mm"
include "ax-mp.mm"
include "exbii.mm"
include "biimpri.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "pwexg.mm"
include "dfac8c.mm"
include "syl.mm"
include "dfac8a.mm"
include "syld.mm"
include "sylc.mm"
include "impbii.mm"

theorem ween
  let cA: class A
  let vr: setvar r
  let vf: setvar f
  let vx: setvar x

  disjoint A r
  disjoint A f
  disjoint A x
  disjoint f r
  disjoint f x
  disjoint r x
  assert |- ( A e. dom card <-> E. r r We A )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    vr
    cv
    #
    wwe
    #
    vr
    wex
    #
    vr
    cA
    dfac8b
    @3
    cA
    cvv
    wcel
    #
    cA
    cpw
    #
    cuni
    #
    @1
    wwe
    #
    vr
    wex
    #
    @0
    @2
    @4
    vr
    @2
    cA
    @1
    wor
    @1
    cvv
    wcel
    @4
    cA
    @1
    weso
    vr
    vex
    cA
    @1
    cvv
    soex
    sylancl
    exlimiv
    @8
    @3
    @7
    @2
    vr
    @6
    cA
    wceq
    @7
    @2
    wb
    cA
    unipw
    @6
    cA
    @1
    weeq2
    ax-mp
    exbii
    biimpri
    @4
    @8
    vx
    cv
    #
    c0
    wne
    @9
    vf
    cv
    cfv
    @9
    wcel
    wi
    vx
    @5
    wral
    vf
    wex
    #
    @0
    @4
    @5
    cvv
    wcel
    @8
    @10
    wi
    cA
    cvv
    pwexg
    vx
    @5
    cvv
    vf
    vr
    dfac8c
    syl
    vx
    cA
    cvv
    vf
    dfac8a
    syld
    sylc
    impbii
end
