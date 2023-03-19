include "cab.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wrex.mm"
include "vex.mm"
include "cplem2.mm"
include "abn0.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "abid.mm"
include "anbi1i.mm"
include "ancom.mm"
include "3bitri.mm"
include "exbii.mm"
include "nfab1.mm"
include "nfcv.mm"
include "nfin.mm"
include "n0f.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "imbi12i.mm"
include "ralbii.mm"
include "mpbi.mm"

theorem cp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph z
  disjoint ph w
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  assert |- E. w A. x e. z ( E. y ph -> E. y e. w ph )

  proof
    wph
    vy
    cab
    #
    c0
    wne
    #
    @0
    vw
    cv
    #
    cin
    #
    c0
    wne
    #
    wi
    #
    vx
    vz
    cv
    #
    wral
    #
    vw
    wex
    wph
    vy
    wex
    #
    wph
    vy
    @2
    wrex
    #
    wi
    #
    vx
    @6
    wral
    #
    vw
    wex
    vx
    vw
    @6
    @0
    vz
    vex
    cplem2
    @7
    @11
    vw
    @5
    @10
    vx
    @6
    @1
    @8
    @4
    @9
    wph
    vy
    abn0
    vy
    cv
    #
    @3
    wcel
    #
    vy
    wex
    @12
    @2
    wcel
    #
    wph
    wa
    #
    vy
    wex
    @4
    @9
    @13
    @15
    vy
    @13
    @12
    @0
    wcel
    #
    @14
    wa
    wph
    @14
    wa
    @15
    @12
    @0
    @2
    elin
    @16
    wph
    @14
    wph
    vy
    abid
    anbi1i
    wph
    @14
    ancom
    3bitri
    exbii
    vy
    @3
    vy
    @0
    @2
    wph
    vy
    nfab1
    vy
    @2
    nfcv
    nfin
    n0f
    wph
    vy
    @2
    df-rex
    3bitr4i
    imbi12i
    ralbii
    exbii
    mpbi
end
