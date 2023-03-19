include "ccnv.mm"
include "cin.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wral.mm"
include "wi.mm"
include "asymref.mm"
include "albiim.mm"
include "ralbii.mm"
include "r19.26.mm"
include "ancom.mm"
include "equcom.mm"
include "imbi1i.mm"
include "albii.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "anidm.mm"
include "syl6bb.mm"
include "equsalvw.mm"
include "bitri.mm"
include "wcel.mm"
include "df-ral.mm"
include "wn.mm"
include "cop.mm"
include "df-br.mm"
include "vex.mm"
include "opeluu.mm"
include "simpld.mm"
include "sylbi.mm"
include "adantr.mm"
include "pm2.24d.mm"
include "com12.mm"
include "alrimiv.mm"
include "id.mm"
include "ja.mm"
include "ax-1.mm"
include "impbii.mm"
include "anbi12i.mm"
include "3bitri.mm"

theorem asymref2
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
  assert |- ( ( R i^i `' R ) = ( _I |` U. U. R ) <-> ( A. x e. U. U. R x R x /\ A. x A. y ( ( x R y /\ y R x ) -> x = y ) ) )

  proof
    cR
    cR
    ccnv
    cin
    cid
    cR
    cuni
    cuni
    #
    cres
    wceq
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @2
    @1
    cR
    wbr
    #
    wa
    #
    @1
    @2
    wceq
    #
    wb
    vy
    wal
    #
    vx
    @0
    wral
    @5
    @6
    wi
    #
    vy
    wal
    #
    @6
    @5
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    @0
    wral
    #
    @1
    @1
    cR
    wbr
    #
    vx
    @0
    wral
    #
    @9
    vx
    wal
    #
    wa
    #
    vx
    vy
    cR
    asymref
    @7
    @12
    vx
    @0
    @5
    @6
    vy
    albiim
    ralbii
    @13
    @9
    vx
    @0
    wral
    #
    @11
    vx
    @0
    wral
    #
    wa
    @19
    @18
    wa
    @17
    @9
    @11
    vx
    @0
    r19.26
    @18
    @19
    ancom
    @19
    @15
    @18
    @16
    @11
    @14
    vx
    @0
    @11
    @2
    @1
    wceq
    #
    @5
    wi
    #
    vy
    wal
    @14
    @10
    @21
    vy
    @6
    @20
    @5
    vx
    vy
    equcom
    imbi1i
    albii
    @5
    @14
    vy
    vx
    @20
    @5
    @14
    @14
    wa
    @14
    @20
    @3
    @14
    @4
    @14
    @2
    @1
    @1
    cR
    breq2
    @2
    @1
    @1
    cR
    breq1
    anbi12d
    @14
    anidm
    syl6bb
    equsalvw
    bitri
    ralbii
    @18
    @1
    @0
    wcel
    #
    @9
    wi
    #
    vx
    wal
    @16
    @9
    vx
    @0
    df-ral
    @23
    @9
    vx
    @23
    @9
    @22
    @9
    @9
    @22
    wn
    #
    @8
    vy
    @5
    @24
    @6
    @5
    @22
    @6
    @3
    @22
    @4
    @3
    @1
    @2
    cop
    cR
    wcel
    #
    @22
    @1
    @2
    cR
    df-br
    @25
    @22
    @2
    @0
    wcel
    @1
    @2
    cR
    vx
    vex
    vy
    vex
    opeluu
    simpld
    sylbi
    adantr
    pm2.24d
    com12
    alrimiv
    @9
    id
    ja
    @9
    @22
    ax-1
    impbii
    albii
    bitri
    anbi12i
    3bitri
    3bitri
end
