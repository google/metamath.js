include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "cab.mm"
include "sbex.mm"
include "sban.mm"
include "nfcri.mm"
include "sbf.mm"
include "nfv.mm"
include "sbrbis.mm"
include "sbalv.mm"
include "anbi12i.mm"
include "bitri.mm"
include "exbii.mm"
include "clabel.mm"
include "sbbii.mm"
include "3bitr4i.mm"

theorem sbabel
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  assume sbabel.1: |- F/_ x A

  disjoint x z
  disjoint y z
  disjoint A v
  disjoint v x
  disjoint v z
  disjoint v y
  disjoint ph v
  assert |- ( [ y / x ] { z | ph } e. A <-> { z | [ y / x ] ph } e. A )

  proof
    vv
    cv
    cA
    wcel
    #
    vz
    vv
    wel
    #
    wph
    wb
    #
    vz
    wal
    #
    wa
    #
    vv
    wex
    #
    vx
    vy
    wsb
    #
    @0
    @1
    wph
    vx
    vy
    wsb
    #
    wb
    #
    vz
    wal
    #
    wa
    #
    vv
    wex
    #
    wph
    vz
    cab
    cA
    wcel
    #
    vx
    vy
    wsb
    @7
    vz
    cab
    cA
    wcel
    @6
    @4
    vx
    vy
    wsb
    #
    vv
    wex
    @11
    @4
    vv
    vx
    vy
    sbex
    @13
    @10
    vv
    @13
    @0
    vx
    vy
    wsb
    #
    @3
    vx
    vy
    wsb
    #
    wa
    @10
    @0
    @3
    vx
    vy
    sban
    @14
    @0
    @15
    @9
    @0
    vx
    vy
    vx
    vv
    cA
    sbabel.1
    nfcri
    sbf
    @2
    @8
    vx
    vy
    vz
    @1
    @1
    wph
    vx
    vy
    @1
    vx
    vy
    @1
    vx
    nfv
    sbf
    sbrbis
    sbalv
    anbi12i
    bitri
    exbii
    bitri
    @12
    @5
    vx
    vy
    wph
    vz
    vv
    cA
    clabel
    sbbii
    @7
    vz
    vv
    cA
    clabel
    3bitr4i
end
