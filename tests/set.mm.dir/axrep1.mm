include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "elequ2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "bibi2d.mm"
include "albidv.mm"
include "imbi2d.mm"
include "ax-rep.mm"
include "19.3v.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "nfv.mm"
include "nfe1.mm"
include "nfbi.mm"
include "nfal.mm"
include "anbi2i.mm"
include "a1i.mm"
include "bibi12d.mm"
include "cbvex.mm"
include "3imtr3i.mm"
include "chvarv.mm"
include "19.35ri.mm"

theorem axrep1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w y
  disjoint ph w
  disjoint w x
  disjoint w z
  assert |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. y /\ ph ) ) )

  proof
    wph
    vz
    vy
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vz
    vx
    wel
    #
    vx
    vy
    wel
    #
    wph
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    vx
    @3
    vx
    wal
    #
    @4
    vx
    vw
    wel
    #
    wph
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    vx
    wex
    #
    wi
    @10
    @9
    vx
    wex
    #
    wi
    vw
    vy
    vw
    vy
    weq
    #
    @16
    @17
    @10
    @18
    @15
    @9
    vx
    @18
    @14
    @8
    vz
    @18
    @13
    @7
    @4
    @18
    @12
    @6
    vx
    @18
    @11
    @5
    wph
    vw
    vy
    vx
    elequ2
    anbi1d
    exbidv
    bibi2d
    albidv
    exbidv
    imbi2d
    wph
    vy
    wal
    #
    @0
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vx
    wal
    vz
    vy
    wel
    #
    @11
    @19
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    vy
    wex
    @10
    @16
    wph
    vw
    vy
    vz
    vx
    ax-rep
    @22
    @3
    vx
    @21
    @2
    vy
    @20
    @1
    vz
    @19
    wph
    @0
    wph
    vy
    19.3v
    #
    imbi1i
    albii
    exbii
    albii
    @27
    @15
    vy
    vx
    @26
    vx
    vz
    @23
    @25
    vx
    @23
    vx
    nfv
    @24
    vx
    nfe1
    nfbi
    nfal
    @15
    vy
    nfv
    vy
    vx
    weq
    #
    @26
    @14
    vz
    @29
    @23
    @4
    @25
    @13
    vy
    vx
    vz
    elequ2
    @25
    @13
    wb
    @29
    @24
    @12
    vx
    @19
    wph
    @11
    @28
    anbi2i
    exbii
    a1i
    bibi12d
    albidv
    cbvex
    3imtr3i
    chvarv
    19.35ri
end
