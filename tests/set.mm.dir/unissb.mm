include "cv.mm"
include "cuni.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "eluni.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "alcom.mm"
include "19.21v.mm"
include "impexp.mm"
include "bi2.04.mm"
include "bitri.mm"
include "dfss2.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "df-ral.mm"

theorem unissb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( U. A C_ B <-> A. x e. A x C_ B )

  proof
    vy
    cv
    #
    cA
    cuni
    #
    wcel
    #
    @0
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    cv
    #
    cA
    wcel
    #
    @6
    cB
    wss
    #
    wi
    #
    vx
    wal
    #
    @1
    cB
    wss
    @8
    vx
    cA
    wral
    @5
    @0
    @6
    wcel
    #
    @7
    wa
    #
    @3
    wi
    #
    vx
    wal
    #
    vy
    wal
    #
    @10
    @4
    @14
    vy
    @4
    @12
    vx
    wex
    #
    @3
    wi
    @14
    @2
    @16
    @3
    vx
    @0
    cA
    eluni
    imbi1i
    @12
    @3
    vx
    19.23v
    bitr4i
    albii
    @15
    @13
    vy
    wal
    #
    vx
    wal
    @10
    @13
    vy
    vx
    alcom
    @17
    @9
    vx
    @7
    @11
    @3
    wi
    #
    wi
    #
    vy
    wal
    @7
    @18
    vy
    wal
    #
    wi
    @17
    @9
    @7
    @18
    vy
    19.21v
    @13
    @19
    vy
    @13
    @11
    @7
    @3
    wi
    wi
    @19
    @11
    @7
    @3
    impexp
    @11
    @7
    @3
    bi2.04
    bitri
    albii
    @8
    @20
    @7
    vy
    @6
    cB
    dfss2
    imbi2i
    3bitr4i
    albii
    bitri
    bitri
    vy
    @1
    cB
    dfss2
    @8
    vx
    cA
    df-ral
    3bitr4i
end
