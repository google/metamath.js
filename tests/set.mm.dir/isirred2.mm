include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "w3a.mm"
include "eldif.mm"
include "wal.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "pm4.56.mm"
include "df-ne.mm"
include "imbi12i.mm"
include "con34b.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "2albii.mm"
include "r2al.mm"
include "3bitr4i.mm"
include "eqid.mm"
include "isirred.mm"
include "df-3an.mm"

theorem isirred2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cX: class X
  assume isirred2.1: |- B = ( Base ` R )
  assume isirred2.2: |- U = ( Unit ` R )
  assume isirred2.3: |- I = ( Irred ` R )
  assume isirred2.4: |- .x. = ( .r ` R )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  assert |- ( X e. I <-> ( X e. B /\ -. X e. U /\ A. x e. B A. y e. B ( ( x .x. y ) = X -> ( x e. U \/ y e. U ) ) ) )

  proof
    cX
    cB
    cU
    cdif
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cX
    wne
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    wa
    cX
    cB
    wcel
    #
    cX
    cU
    wcel
    wn
    #
    wa
    #
    @4
    cX
    wceq
    #
    @2
    cU
    wcel
    #
    @3
    cU
    wcel
    #
    wo
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    cX
    cI
    wcel
    @7
    @8
    @15
    w3a
    @1
    @9
    @6
    @15
    cX
    cB
    cU
    eldif
    @2
    @0
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    #
    @5
    wi
    #
    vy
    wal
    vx
    wal
    @2
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    @14
    wi
    #
    vy
    wal
    vx
    wal
    @6
    @15
    @19
    @23
    vx
    vy
    @19
    @22
    @11
    wn
    #
    @12
    wn
    #
    wa
    #
    wa
    #
    @5
    wi
    #
    @23
    @18
    @27
    @5
    @18
    @20
    @24
    wa
    #
    @21
    @25
    wa
    #
    wa
    @27
    @16
    @29
    @17
    @30
    @2
    cB
    cU
    eldif
    @3
    cB
    cU
    eldif
    anbi12i
    @20
    @24
    @21
    @25
    an4
    bitri
    imbi1i
    @28
    @22
    @26
    @5
    wi
    #
    wi
    @23
    @22
    @26
    @5
    impexp
    @31
    @14
    @22
    @31
    @13
    wn
    #
    @10
    wn
    #
    wi
    @14
    @26
    @32
    @5
    @33
    @11
    @12
    pm4.56
    @4
    cX
    df-ne
    imbi12i
    @10
    @13
    con34b
    bitr4i
    imbi2i
    bitri
    bitri
    2albii
    @5
    vx
    vy
    @0
    @0
    r2al
    @14
    vx
    vy
    cB
    cB
    r2al
    3bitr4i
    anbi12i
    vx
    vy
    cB
    cR
    c.x
    cU
    cI
    @0
    cX
    isirred2.1
    isirred2.2
    isirred2.3
    @0
    eqid
    isirred2.4
    isirred
    @7
    @8
    @15
    df-3an
    3bitr4i
end
