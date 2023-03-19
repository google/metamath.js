include "wal.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "nfe1.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfan.mm"
include "nfex.mm"
include "nfbi.mm"
include "nfal.mm"
include "nfim.mm"
include "elequ2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "bibi2d.mm"
include "albidv.mm"
include "imbi2d.mm"
include "axrepnd.mm"
include "19.3v.mm"
include "anbi1i.mm"
include "exbii.mm"
include "bibi12i.mm"
include "albii.mm"
include "imbi2i.mm"
include "mpbi.mm"
include "chvar.mm"
include "19.35i.mm"
include "19.3.mm"
include "anbi2i.mm"
include "a1i.mm"
include "bibi12d.mm"
include "cbvex.mm"
include "sylib.mm"

theorem zfcndrep
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  assert |- ( A. w E. y A. z ( A. y ph -> z = y ) -> E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) )

  proof
    wph
    vy
    wal
    #
    vz
    cv
    #
    vy
    cv
    #
    wceq
    wi
    vz
    wal
    #
    vy
    wex
    #
    vw
    wal
    @1
    vw
    cv
    #
    wcel
    #
    @5
    vx
    cv
    #
    wcel
    #
    @0
    vy
    wal
    #
    wa
    #
    vw
    wex
    #
    wb
    #
    vz
    wal
    #
    vw
    wex
    @1
    @2
    wcel
    #
    @8
    @0
    wa
    #
    vw
    wex
    #
    wb
    #
    vz
    wal
    #
    vy
    wex
    @4
    @13
    vw
    @4
    @6
    @5
    @2
    wcel
    #
    @9
    wa
    #
    vw
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    vw
    wex
    #
    @4
    @13
    wi
    #
    vw
    wex
    vy
    vx
    @26
    vy
    vw
    @4
    @13
    vy
    @3
    vy
    nfe1
    @12
    vy
    vz
    @6
    @11
    vy
    @6
    vy
    nfv
    @10
    vy
    vw
    @8
    @9
    vy
    @8
    vy
    nfv
    @0
    vy
    nfa1
    nfan
    nfex
    nfbi
    nfal
    #
    nfim
    nfex
    @2
    @7
    wceq
    #
    @24
    @26
    vw
    @28
    @23
    @13
    @4
    @28
    @22
    @12
    vz
    @28
    @21
    @11
    @6
    @28
    @20
    @10
    vw
    @28
    @19
    @8
    @9
    vy
    vx
    vw
    elequ2
    anbi1d
    exbidv
    bibi2d
    albidv
    imbi2d
    exbidv
    @4
    @6
    vy
    wal
    #
    @19
    vz
    wal
    #
    @9
    wa
    #
    vw
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    vw
    wex
    @25
    @0
    vw
    vy
    vz
    axrepnd
    @35
    @24
    vw
    @34
    @23
    @4
    @33
    @22
    vz
    @29
    @6
    @32
    @21
    @6
    vy
    19.3v
    @31
    @20
    vw
    @30
    @19
    @9
    @19
    vz
    19.3v
    anbi1i
    exbii
    bibi12i
    albii
    imbi2i
    exbii
    mpbi
    chvar
    19.35i
    @13
    @18
    vw
    vy
    @27
    @17
    vw
    vz
    @14
    @16
    vw
    @14
    vw
    nfv
    @15
    vw
    nfe1
    nfbi
    nfal
    @5
    @2
    wceq
    #
    @12
    @17
    vz
    @36
    @6
    @14
    @11
    @16
    vw
    vy
    vz
    elequ2
    @11
    @16
    wb
    @36
    @10
    @15
    vw
    @9
    @0
    @8
    @0
    vy
    wph
    vy
    nfa1
    19.3
    anbi2i
    exbii
    a1i
    bibi12d
    albidv
    cbvex
    sylib
end
