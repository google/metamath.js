include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cv.mm"
include "weu.mm"
include "cbvexv.mm"
include "isseti.mm"
include "biantrur.mm"
include "exbii.mm"
include "19.41v.mm"
include "excom.mm"
include "3bitr2i.mm"
include "bitri.mm"
include "wb.mm"
include "eqeq2.mm"
include "imim2i.mm"
include "biimpr.mm"
include "an31.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitr3i.mm"
include "sylib.mm"
include "syl.mm"
include "2alimi.mm"
include "19.23v.mm"
include "albii.mm"
include "19.21v.mm"
include "eximdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "pm4.24.mm"
include "biimpi.mm"
include "prth.mm"
include "eqtr3.mm"
include "syl56.mm"
include "alanimi.mm"
include "com12.mm"
include "alrimivv.mm"
include "adantl.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "albidv.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem euind
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume euind.1: |- B e. _V
  assume euind.2: |- ( x = y -> ( ph <-> ps ) )
  assume euind.3: |- ( x = y -> A = B )

  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint x z
  disjoint ps x
  disjoint ps z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint A w
  disjoint w x
  assert |- ( ( A. x A. y ( ( ph /\ ps ) -> A = B ) /\ E. x ph ) -> E! z A. x ( ph -> z = A ) )

  proof
    wph
    wps
    wa
    #
    cA
    cB
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wph
    vx
    wex
    #
    wa
    wph
    vz
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    vz
    wex
    #
    @8
    wph
    vw
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    @5
    @10
    wceq
    #
    wi
    #
    vw
    wal
    vz
    wal
    #
    @8
    vz
    weu
    @3
    @4
    @9
    @4
    @5
    cB
    wceq
    #
    wps
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    @3
    @9
    @4
    wps
    vy
    wex
    #
    @21
    wph
    wps
    vx
    vy
    euind.2
    cbvexv
    @22
    @18
    vz
    wex
    #
    wps
    wa
    #
    vy
    wex
    @19
    vz
    wex
    #
    vy
    wex
    @21
    wps
    @24
    vy
    @23
    wps
    vz
    cB
    euind.1
    isseti
    biantrur
    exbii
    @25
    @24
    vy
    @18
    wps
    vz
    19.41v
    exbii
    @19
    vy
    vz
    excom
    3bitr2i
    bitri
    @3
    @20
    @8
    vz
    @3
    @19
    @7
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @20
    @8
    wi
    #
    @2
    @26
    vx
    vy
    @2
    @0
    @6
    @18
    wb
    #
    wi
    #
    @26
    @1
    @30
    @0
    cA
    cB
    @5
    eqeq2
    imim2i
    @31
    @0
    @18
    @6
    wi
    #
    wi
    #
    @26
    @30
    @32
    @0
    @6
    @18
    biimpr
    imim2i
    @0
    @18
    wa
    #
    @6
    wi
    @19
    wph
    wa
    #
    @6
    wi
    @33
    @26
    @34
    @35
    @6
    wph
    wps
    @18
    an31
    imbi1i
    @0
    @18
    @6
    impexp
    @19
    wph
    @6
    impexp
    3bitr3i
    sylib
    syl
    2alimi
    @28
    @20
    @7
    wi
    #
    vx
    wal
    @29
    @27
    @36
    vx
    @19
    @7
    vy
    19.23v
    albii
    @20
    @7
    vx
    19.21v
    bitri
    sylib
    eximdv
    syl5bi
    imp
    @4
    @17
    @3
    @4
    @16
    vz
    vw
    @14
    @4
    @15
    @14
    wph
    @15
    wi
    #
    vx
    wal
    @4
    @15
    wi
    @7
    @12
    @37
    vx
    wph
    wph
    wph
    wa
    #
    @7
    @12
    wa
    @6
    @11
    wa
    @15
    wph
    @38
    wph
    pm4.24
    biimpi
    wph
    @6
    wph
    @11
    prth
    @5
    @10
    cA
    eqtr3
    syl56
    alanimi
    wph
    @15
    vx
    19.23v
    sylib
    com12
    alrimivv
    adantl
    @8
    @13
    vz
    vw
    @15
    @7
    @12
    vx
    @15
    @6
    @11
    wph
    @5
    @10
    cA
    eqeq1
    imbi2d
    albidv
    eu4
    sylanbrc
end
