include "whe.mm"
include "cima.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "df-he.mm"
include "wa.mm"
include "wex.mm"
include "19.21v.mm"
include "bicomi.mm"
include "albii.mm"
include "alcom.mm"
include "impexp.mm"
include "19.23v.mm"
include "bitri.mm"
include "3bitri.mm"
include "cop.mm"
include "cab.mm"
include "dfss2.mm"
include "vex.mm"
include "weq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab.mm"
include "imbi1i.mm"
include "bitr2i.mm"
include "dfima3.mm"
include "eqcomi.mm"
include "sseq1i.mm"

theorem dfhe3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint R z
  assert |- ( R hereditary A <-> A. x ( x e. A -> A. y ( x R y -> y e. A ) ) )

  proof
    cA
    cR
    whe
    cR
    cA
    cima
    #
    cA
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    @2
    vy
    cv
    #
    cR
    wbr
    #
    @4
    cA
    wcel
    #
    wi
    #
    vy
    wal
    wi
    #
    vx
    wal
    #
    cA
    cR
    df-he
    @9
    @3
    @5
    wa
    #
    vx
    wex
    #
    @6
    wi
    #
    vy
    wal
    #
    @1
    @9
    @3
    @7
    wi
    #
    vy
    wal
    #
    vx
    wal
    @14
    vx
    wal
    #
    vy
    wal
    @13
    @8
    @15
    vx
    @15
    @8
    @3
    @7
    vy
    19.21v
    bicomi
    albii
    @14
    vx
    vy
    alcom
    @16
    @12
    vy
    @16
    @10
    @6
    wi
    #
    vx
    wal
    @12
    @14
    @17
    vx
    @17
    @14
    @3
    @5
    @6
    impexp
    bicomi
    albii
    @10
    @6
    vx
    19.23v
    bitri
    albii
    3bitri
    @13
    @3
    @2
    vz
    cv
    #
    cop
    #
    cR
    wcel
    #
    wa
    #
    vx
    wex
    #
    vz
    cab
    #
    cA
    wss
    #
    @1
    @24
    @4
    @23
    wcel
    #
    @6
    wi
    #
    vy
    wal
    @13
    vy
    @23
    cA
    dfss2
    @26
    @12
    vy
    @25
    @11
    @6
    @22
    @11
    vz
    @4
    vy
    vex
    vz
    vy
    weq
    #
    @21
    @10
    vx
    @27
    @20
    @5
    @3
    @27
    @20
    @2
    @4
    cop
    #
    cR
    wcel
    @5
    @27
    @19
    @28
    cR
    @18
    @4
    @2
    opeq2
    eleq1d
    @2
    @4
    cR
    df-br
    syl6bbr
    anbi2d
    exbidv
    elab
    imbi1i
    albii
    bitr2i
    @23
    @0
    cA
    @0
    @23
    vx
    vz
    cR
    cA
    dfima3
    eqcomi
    sseq1i
    bitri
    bitr2i
    bitri
end
