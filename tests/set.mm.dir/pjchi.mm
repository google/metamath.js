include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "c0v.mm"
include "cva.mm"
include "co.mm"
include "chil.mm"
include "pjhclii.mm"
include "ax-hvaddid.mm"
include "ax-mp.mm"
include "cort.mm"
include "pjpji.mm"
include "pjoc1i.mm"
include "biimpi.mm"
include "oveq2d.mm"
include "syl5req.mm"
include "syl5eqr.mm"
include "pjclii.mm"
include "eleq1.mm"
include "mpbii.mm"
include "impbii.mm"

theorem pjchi
  let cA: class A
  let cH: class H
  assume pjop.1: |- H e. CH
  assume pjop.2: |- A e. ~H


  assert |- ( A e. H <-> ( ( projh ` H ) ` A ) = A )

  proof
    cA
    cH
    wcel
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cA
    wceq
    #
    @0
    @1
    @1
    c0v
    cva
    co
    #
    cA
    @1
    chil
    wcel
    @3
    @1
    wceq
    cA
    cH
    pjop.1
    pjop.2
    pjhclii
    @1
    ax-hvaddid
    ax-mp
    @0
    cA
    @1
    cA
    cH
    cort
    cfv
    cpjh
    cfv
    cfv
    #
    cva
    co
    @3
    cA
    cH
    pjop.1
    pjop.2
    pjpji
    @0
    @4
    c0v
    @1
    cva
    @0
    @4
    c0v
    wceq
    cA
    cH
    pjop.1
    pjop.2
    pjoc1i
    biimpi
    oveq2d
    syl5req
    syl5eqr
    @2
    @1
    cH
    wcel
    @0
    cA
    cH
    pjop.1
    pjop.2
    pjclii
    @1
    cA
    cH
    eleq1
    mpbii
    impbii
end
