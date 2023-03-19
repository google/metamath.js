include "cv.mm"
include "cop.mm"
include "ccnv.mm"
include "cin.mm"
include "wcel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wb.mm"
include "wal.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "df-br.mm"
include "vex.mm"
include "opeluu.mm"
include "sylbi.mm"
include "simpld.mm"
include "adantr.mm"
include "pm4.71ri.mm"
include "bibi1i.mm"
include "elin.mm"
include "brcnv.mm"
include "bitr3i.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "opelres.mm"
include "ideq.mm"
include "anbi2ci.mm"
include "bitri.mm"
include "bibi12i.mm"
include "pm5.32.mm"
include "3bitr4i.mm"
include "albii.mm"
include "19.21v.mm"
include "wrel.mm"
include "relcnv.mm"
include "relin2.mm"
include "ax-mp.mm"
include "relres.mm"
include "eqrel.mm"
include "mp2an.mm"
include "df-ral.mm"

theorem asymref
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V z
  disjoint W z
  assert |- ( ( R i^i `' R ) = ( _I |` U. U. R ) <-> A. x e. U. U. R A. y ( ( x R y /\ y R x ) <-> x = y ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cR
    cR
    ccnv
    #
    cin
    #
    wcel
    #
    @2
    cid
    cR
    cuni
    cuni
    #
    cres
    #
    wcel
    #
    wb
    #
    vy
    wal
    #
    vx
    wal
    #
    @0
    @6
    wcel
    #
    @0
    @1
    cR
    wbr
    #
    @1
    @0
    cR
    wbr
    #
    wa
    #
    @0
    @1
    wceq
    #
    wb
    #
    vy
    wal
    #
    wi
    #
    vx
    wal
    @4
    @7
    wceq
    #
    @18
    vx
    @6
    wral
    @10
    @19
    vx
    @10
    @12
    @17
    wi
    #
    vy
    wal
    @19
    @9
    @21
    vy
    @15
    @12
    @16
    wa
    #
    wb
    @12
    @15
    wa
    #
    @22
    wb
    @9
    @21
    @15
    @23
    @22
    @15
    @12
    @13
    @12
    @14
    @13
    @12
    @1
    @6
    wcel
    #
    @13
    @2
    cR
    wcel
    #
    @12
    @24
    wa
    @0
    @1
    cR
    df-br
    #
    @0
    @1
    cR
    vx
    vex
    #
    vy
    vex
    #
    opeluu
    sylbi
    simpld
    adantr
    pm4.71ri
    bibi1i
    @5
    @15
    @8
    @22
    @5
    @25
    @2
    @3
    wcel
    #
    wa
    @15
    @2
    cR
    @3
    elin
    @13
    @25
    @14
    @29
    @26
    @14
    @0
    @1
    @3
    wbr
    @29
    @0
    @1
    cR
    @27
    @28
    brcnv
    @0
    @1
    @3
    df-br
    bitr3i
    anbi12i
    bitr4i
    @8
    @2
    cid
    wcel
    #
    @12
    wa
    @22
    @0
    @1
    cid
    @6
    @28
    opelres
    @30
    @16
    @12
    @30
    @0
    @1
    cid
    wbr
    @16
    @0
    @1
    cid
    df-br
    @0
    @1
    @28
    ideq
    bitr3i
    anbi2ci
    bitri
    bibi12i
    @12
    @15
    @16
    pm5.32
    3bitr4i
    albii
    @12
    @17
    vy
    19.21v
    bitri
    albii
    @4
    wrel
    #
    @7
    wrel
    @20
    @11
    wb
    @3
    wrel
    @31
    cR
    relcnv
    cR
    @3
    relin2
    ax-mp
    cid
    @6
    relres
    vx
    vy
    @4
    @7
    eqrel
    mp2an
    @18
    vx
    @6
    df-ral
    3bitr4i
end
