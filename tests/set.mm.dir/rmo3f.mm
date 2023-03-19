include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "df-rmo.mm"
include "wal.mm"
include "sban.mm"
include "clelsb3f.mm"
include "anbi1i.mm"
include "bitri.mm"
include "anbi2i.mm"
include "an4.mm"
include "ancom.mm"
include "3bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "nfcri.mm"
include "r19.21.mm"
include "3bitr2i.mm"
include "nfan.mm"
include "mo3.mm"
include "3bitr4i.mm"

theorem rmo3f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rmo3f.1: |- F/_ x A
  assume rmo3f.2: |- F/_ y A
  assume rmo3f.3: |- F/ y ph

  disjoint x y
  assert |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) )

  proof
    wph
    vx
    cA
    wrmo
    vx
    cv
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
    wph
    vx
    vy
    wsb
    #
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
    @1
    @1
    vx
    vy
    wsb
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
    @0
    @7
    wi
    #
    vx
    wal
    @2
    @8
    @12
    @13
    vx
    @12
    vy
    cv
    cA
    wcel
    #
    @0
    @6
    wi
    #
    wi
    #
    vy
    wal
    @15
    vy
    cA
    wral
    @13
    @11
    @16
    vy
    @11
    @14
    @0
    wa
    #
    @4
    wa
    #
    @5
    wi
    @17
    @6
    wi
    @16
    @10
    @18
    @5
    @10
    @1
    @14
    @3
    wa
    #
    wa
    @0
    @14
    wa
    #
    @4
    wa
    @18
    @9
    @19
    @1
    @9
    @0
    vx
    vy
    wsb
    #
    @3
    wa
    @19
    @0
    wph
    vx
    vy
    sban
    @21
    @14
    @3
    vy
    vx
    cA
    rmo3f.1
    clelsb3f
    anbi1i
    bitri
    anbi2i
    @0
    wph
    @14
    @3
    an4
    @20
    @17
    @4
    @0
    @14
    ancom
    anbi1i
    3bitri
    imbi1i
    @17
    @4
    @5
    impexp
    @14
    @0
    @6
    impexp
    3bitri
    albii
    @15
    vy
    cA
    df-ral
    @0
    @6
    vy
    cA
    vy
    vx
    cA
    rmo3f.2
    nfcri
    #
    r19.21
    3bitr2i
    albii
    @1
    vx
    vy
    @0
    wph
    vy
    @22
    rmo3f.3
    nfan
    mo3
    @7
    vx
    cA
    df-ral
    3bitr4i
    bitri
end
