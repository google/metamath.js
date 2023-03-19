include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "eliunxp.mm"
include "imbi1i.mm"
include "19.23vv.mm"
include "bitr4i.mm"
include "albii.mm"
include "alrot3.mm"
include "impexp.mm"
include "opex.mm"
include "imbi2d.mm"
include "ceqsalv.mm"
include "bitri.mm"
include "2albii.mm"
include "df-ral.mm"
include "r2al.mm"
include "3bitr4i.mm"

theorem raliunxp
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ralxp.1: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  assert |- ( A. x e. U_ y e. A ( { y } X. B ) ph <-> A. y e. A A. z e. B ps )

  proof
    vx
    cv
    #
    vy
    cA
    vy
    cv
    #
    csn
    cB
    cxp
    ciun
    #
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    @1
    cA
    wcel
    vz
    cv
    #
    cB
    wcel
    wa
    #
    wps
    wi
    #
    vz
    wal
    vy
    wal
    #
    wph
    vx
    @2
    wral
    wps
    vz
    cB
    wral
    vy
    cA
    wral
    @5
    @0
    @1
    @6
    cop
    #
    wceq
    #
    @7
    wa
    #
    wph
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    @9
    @4
    @14
    vx
    @4
    @12
    vz
    wex
    vy
    wex
    #
    wph
    wi
    @14
    @3
    @16
    wph
    vy
    vz
    cA
    cB
    @0
    eliunxp
    imbi1i
    @12
    wph
    vy
    vz
    19.23vv
    bitr4i
    albii
    @15
    @13
    vx
    wal
    #
    vz
    wal
    vy
    wal
    @9
    @13
    vx
    vy
    vz
    alrot3
    @17
    @8
    vy
    vz
    @17
    @11
    @7
    wph
    wi
    #
    wi
    #
    vx
    wal
    @8
    @13
    @19
    vx
    @11
    @7
    wph
    impexp
    albii
    @18
    @8
    vx
    @10
    @1
    @6
    opex
    @11
    wph
    wps
    @7
    ralxp.1
    imbi2d
    ceqsalv
    bitri
    2albii
    bitri
    bitri
    wph
    vx
    @2
    df-ral
    wps
    vy
    vz
    cA
    cB
    r2al
    3bitr4i
end
