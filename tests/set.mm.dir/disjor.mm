include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "df-disj.mm"
include "wa.mm"
include "wi.mm"
include "ralcom4.mm"
include "wn.mm"
include "orcom.mm"
include "df-or.mm"
include "wex.mm"
include "neq0.mm"
include "elin.mm"
include "exbii.mm"
include "bitri.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "ralbii.mm"
include "eleq2d.mm"
include "rmo4.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem disjor
  let cA: class A
  let cB: class B
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  assume disjor.1: |- ( i = j -> B = C )

  disjoint i j
  disjoint A i
  disjoint A j
  disjoint B j
  disjoint C i
  disjoint i x
  disjoint j x
  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( Disj_ i e. A B <-> A. i e. A A. j e. A ( i = j \/ ( B i^i C ) = (/) ) )

  proof
    vi
    cA
    cB
    wdisj
    vx
    cv
    #
    cB
    wcel
    #
    vi
    cA
    wrmo
    #
    vx
    wal
    #
    vi
    vj
    weq
    #
    cB
    cC
    cin
    #
    c0
    wceq
    #
    wo
    #
    vj
    cA
    wral
    #
    vi
    cA
    wral
    #
    vi
    vx
    cA
    cB
    df-disj
    @1
    @0
    cC
    wcel
    #
    wa
    #
    @4
    wi
    #
    vj
    cA
    wral
    #
    vx
    wal
    #
    vi
    cA
    wral
    @13
    vi
    cA
    wral
    #
    vx
    wal
    @9
    @3
    @13
    vi
    vx
    cA
    ralcom4
    @8
    @14
    vi
    cA
    @8
    @12
    vx
    wal
    #
    vj
    cA
    wral
    @14
    @7
    @16
    vj
    cA
    @7
    @6
    @4
    wo
    @6
    wn
    #
    @4
    wi
    #
    @16
    @4
    @6
    orcom
    @6
    @4
    df-or
    @18
    @11
    vx
    wex
    #
    @4
    wi
    @16
    @17
    @19
    @4
    @17
    @0
    @5
    wcel
    #
    vx
    wex
    @19
    vx
    @5
    neq0
    @20
    @11
    vx
    @0
    cB
    cC
    elin
    exbii
    bitri
    imbi1i
    @11
    @4
    vx
    19.23v
    bitr4i
    3bitri
    ralbii
    @12
    vj
    vx
    cA
    ralcom4
    bitri
    ralbii
    @2
    @15
    vx
    @1
    @10
    vi
    vj
    cA
    @4
    cB
    cC
    @0
    disjor.1
    eleq2d
    rmo4
    albii
    3bitr4i
    bitr4i
end
