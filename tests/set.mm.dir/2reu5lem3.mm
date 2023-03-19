include "wreu.mm"
include "wrmo.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "weu.mm"
include "wmo.mm"
include "wal.mm"
include "wex.mm"
include "weq.mm"
include "wi.mm"
include "wrex.mm"
include "2reu5lem1.mm"
include "2reu5lem2.mm"
include "anbi12i.mm"
include "2eu5.mm"
include "3anass.mm"
include "exbii.mm"
include "19.42v.mm"
include "df-rex.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "bitr4i.mm"
include "3anan12.mm"
include "imbi1i.mm"
include "impexp.mm"
include "imbi2i.mm"
include "albii.mm"
include "df-ral.mm"
include "r19.21v.mm"
include "3bitr2i.mm"

theorem 2reu5lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B

  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint ph w
  disjoint ph z
  assert |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph ) <-> ( E. x e. A E. y e. B ph /\ E. z E. w A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) )

  proof
    wph
    vy
    cB
    wreu
    vx
    cA
    wreu
    #
    wph
    vy
    cB
    wrmo
    vx
    cA
    wral
    #
    wa
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wph
    w3a
    #
    vy
    weu
    vx
    weu
    #
    @4
    vy
    wmo
    vx
    wal
    #
    wa
    @4
    vy
    wex
    #
    vx
    wex
    #
    @4
    vx
    vz
    weq
    vy
    vw
    weq
    wa
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    vw
    wex
    #
    vz
    wex
    #
    wa
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    wph
    @9
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vw
    wex
    #
    vz
    wex
    #
    wa
    @0
    @5
    @1
    @6
    wph
    vx
    vy
    cA
    cB
    2reu5lem1
    wph
    vx
    vy
    cA
    cB
    2reu5lem2
    anbi12i
    @4
    vx
    vy
    vz
    vw
    2eu5
    @8
    @16
    @14
    @21
    @8
    @2
    @15
    wa
    #
    vx
    wex
    @16
    @7
    @22
    vx
    @7
    @2
    @3
    wph
    wa
    #
    wa
    #
    vy
    wex
    @2
    @23
    vy
    wex
    #
    wa
    @22
    @4
    @24
    vy
    @2
    @3
    wph
    3anass
    exbii
    @2
    @23
    vy
    19.42v
    @25
    @15
    @2
    @15
    @25
    wph
    vy
    cB
    df-rex
    bicomi
    anbi2i
    3bitri
    exbii
    @15
    vx
    cA
    df-rex
    bitr4i
    @13
    @20
    vz
    @12
    @19
    vw
    @12
    @2
    @18
    wi
    #
    vx
    wal
    @19
    @11
    @26
    vx
    @11
    @3
    @2
    @17
    wi
    #
    wi
    #
    vy
    wal
    @27
    vy
    cB
    wral
    @26
    @10
    @28
    vy
    @10
    @3
    @2
    wph
    wa
    #
    wa
    #
    @9
    wi
    @3
    @29
    @9
    wi
    #
    wi
    @28
    @4
    @30
    @9
    @2
    @3
    wph
    3anan12
    imbi1i
    @3
    @29
    @9
    impexp
    @31
    @27
    @3
    @2
    wph
    @9
    impexp
    imbi2i
    3bitri
    albii
    @27
    vy
    cB
    df-ral
    @2
    @17
    vy
    cB
    r19.21v
    3bitr2i
    albii
    @18
    vx
    cA
    df-ral
    bitr4i
    exbii
    exbii
    anbi12i
    3bitri
end
