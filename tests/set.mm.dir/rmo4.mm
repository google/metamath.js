include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "df-rmo.mm"
include "wal.mm"
include "an4.mm"
include "ancom.mm"
include "anbi1i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitri.mm"
include "albii.mm"
include "df-ral.mm"
include "r19.21v.mm"
include "3bitr2i.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "mo4.mm"
include "3bitr4i.mm"

theorem rmo4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume rmo4.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint ps z
  assert |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) )

  proof
    wph
    vx
    cA
    wrmo
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    #
    wph
    wps
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    df-rmo
    @2
    vy
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    wa
    #
    @5
    wi
    #
    vy
    wal
    #
    vx
    wal
    @1
    @7
    wi
    #
    vx
    wal
    @3
    @8
    @14
    @15
    vx
    @14
    @10
    @1
    @6
    wi
    #
    wi
    #
    vy
    wal
    @16
    vy
    cA
    wral
    @15
    @13
    @17
    vy
    @13
    @10
    @1
    wa
    #
    @4
    wa
    #
    @5
    wi
    @18
    @6
    wi
    @17
    @12
    @19
    @5
    @12
    @1
    @10
    wa
    #
    @4
    wa
    @19
    @1
    wph
    @10
    wps
    an4
    @20
    @18
    @4
    @1
    @10
    ancom
    anbi1i
    bitri
    imbi1i
    @18
    @4
    @5
    impexp
    @10
    @1
    @6
    impexp
    3bitri
    albii
    @16
    vy
    cA
    df-ral
    @1
    @6
    vy
    cA
    r19.21v
    3bitr2i
    albii
    @2
    @11
    vx
    vy
    @5
    @1
    @10
    wph
    wps
    @0
    @9
    cA
    eleq1
    rmo4.1
    anbi12d
    mo4
    @7
    vx
    cA
    df-ral
    3bitr4i
    bitri
end
