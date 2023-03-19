include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "bi2.04.mm"
include "impexp.mm"
include "neor.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"
include "wb.mm"
include "nngt1ne1.mm"
include "adantl.mm"
include "anbi1d.mm"
include "cz.mm"
include "nnz.mm"
include "wn.mm"
include "cr.mm"
include "nnre.mm"
include "gtndiv.mm"
include "3expia.mm"
include "sylan.mm"
include "con2d.mm"
include "lenlt.mm"
include "syl2an.mm"
include "sylibrd.mm"
include "ancoms.mm"
include "syl5.mm"
include "pm4.71rd.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "bitr3d.mm"
include "imbi1d.mm"
include "syl5bb.mm"
include "ralbidva.mm"

theorem prime
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. NN -> ( A. x e. NN ( ( A / x ) e. NN -> ( x = 1 \/ x = A ) ) <-> A. x e. NN ( ( 1 < x /\ x <_ A /\ ( A / x ) e. NN ) -> x = A ) ) )

  proof
    cA
    cn
    wcel
    #
    cA
    vx
    cv
    #
    cdiv
    co
    #
    cn
    wcel
    #
    @1
    c1
    wceq
    @1
    cA
    wceq
    #
    wo
    #
    wi
    #
    c1
    @1
    clt
    wbr
    #
    @1
    cA
    cle
    wbr
    #
    @3
    w3a
    #
    @4
    wi
    #
    vx
    cn
    @6
    @1
    c1
    wne
    #
    @3
    wa
    #
    @4
    wi
    #
    @0
    @1
    cn
    wcel
    #
    wa
    #
    @10
    @11
    @3
    @4
    wi
    wi
    @3
    @11
    @4
    wi
    #
    wi
    @13
    @6
    @11
    @3
    @4
    bi2.04
    @11
    @3
    @4
    impexp
    @5
    @16
    @3
    @4
    @1
    c1
    neor
    imbi2i
    3bitr4ri
    @15
    @12
    @9
    @4
    @15
    @7
    @3
    wa
    #
    @12
    @9
    @15
    @7
    @11
    @3
    @14
    @7
    @11
    wb
    @0
    @1
    nngt1ne1
    adantl
    anbi1d
    @15
    @17
    @7
    @8
    @3
    wa
    #
    wa
    @9
    @15
    @3
    @18
    @7
    @15
    @3
    @8
    @3
    @2
    cz
    wcel
    #
    @15
    @8
    @2
    nnz
    @14
    @0
    @19
    @8
    wi
    @14
    @0
    wa
    #
    @19
    cA
    @1
    clt
    wbr
    #
    wn
    #
    @8
    @20
    @21
    @19
    @14
    @1
    cr
    wcel
    #
    @0
    @21
    @19
    wn
    #
    wi
    @1
    nnre
    #
    @23
    @0
    @21
    @24
    @1
    cA
    gtndiv
    3expia
    sylan
    con2d
    @14
    @23
    cA
    cr
    wcel
    @8
    @22
    wb
    @0
    @25
    cA
    nnre
    @1
    cA
    lenlt
    syl2an
    sylibrd
    ancoms
    syl5
    pm4.71rd
    anbi2d
    @7
    @8
    @3
    3anass
    syl6bbr
    bitr3d
    imbi1d
    syl5bb
    ralbidva
end
