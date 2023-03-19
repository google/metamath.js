include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wmo.mm"
include "an4.mm"
include "ancom.mm"
include "anbi1i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitri.mm"
include "albii.mm"
include "df-ral.mm"
include "nfcv.mm"
include "nfel.mm"
include "r19.21.mm"
include "3bitr2i.mm"
include "wsb.mm"
include "nfv.mm"
include "nfan.mm"
include "mo3.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "sbie.mm"
include "anbi2i.mm"
include "2albii.mm"
include "3bitr4i.mm"

theorem rmo4fOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rmo4f.1: |- F/_ x A
  assume rmo4f.2: |- F/_ y A
  assume rmo4f.3: |- F/ x ps
  assume rmo4f.4: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  assert |- ( E* x ( x e. A /\ ph ) <-> A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
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
    @0
    @3
    wceq
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @1
    wph
    wps
    wa
    #
    @7
    wi
    #
    vy
    cA
    wral
    #
    wi
    #
    vx
    wal
    @2
    vx
    wmo
    #
    @13
    vx
    cA
    wral
    @9
    @14
    vx
    @9
    @4
    @1
    @12
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
    @14
    @8
    @17
    vy
    @8
    @4
    @1
    wa
    #
    @11
    wa
    #
    @7
    wi
    @18
    @12
    wi
    @17
    @6
    @19
    @7
    @6
    @1
    @4
    wa
    #
    @11
    wa
    @19
    @1
    wph
    @4
    wps
    an4
    @20
    @18
    @11
    @1
    @4
    ancom
    anbi1i
    bitri
    imbi1i
    @18
    @11
    @7
    impexp
    @4
    @1
    @12
    impexp
    3bitri
    albii
    @16
    vy
    cA
    df-ral
    @1
    @12
    vy
    cA
    vy
    @0
    cA
    vy
    @0
    nfcv
    rmo4f.2
    nfel
    #
    r19.21
    3bitr2i
    albii
    @15
    @2
    @2
    vx
    vy
    wsb
    #
    wa
    #
    @7
    wi
    #
    vy
    wal
    vx
    wal
    @10
    @2
    vx
    vy
    @1
    wph
    vy
    @21
    wph
    vy
    nfv
    nfan
    mo3
    @24
    @8
    vx
    vy
    @23
    @6
    @7
    @22
    @5
    @2
    @2
    @5
    vx
    vy
    @4
    wps
    vx
    vx
    @3
    cA
    vx
    @3
    nfcv
    rmo4f.1
    nfel
    rmo4f.3
    nfan
    @7
    @1
    @4
    wph
    wps
    @0
    @3
    cA
    eleq1
    rmo4f.4
    anbi12d
    sbie
    anbi2i
    imbi1i
    2albii
    bitri
    @13
    vx
    cA
    df-ral
    3bitr4i
end
