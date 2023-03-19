include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "w-bnj15.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "biimpi.mm"
include "bnj837.mm"
include "ancli.mm"
include "19.42v.mm"
include "sylibr.mm"
include "wi.mm"
include "w3a.mm"
include "3simpc.mm"
include "anbi2i.mm"
include "sylib.mm"
include "19.8a.mm"
include "syl.mm"
include "df-rex.mm"
include "3comr.mm"
include "3expib.mm"
include "simp1.mm"
include "simp2.mm"
include "rexnal.mm"
include "bicomi.mm"
include "xchnxbir.mm"
include "notnotb.mm"
include "rexbii.mm"
include "bitr4i.mm"
include "bnj1196.mm"
include "3ad2ant3.mm"
include "3anass.mm"
include "exbii.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "bnj1198.mm"
include "bnj1190.mm"
include "bnj593.mm"
include "bnj937.mm"
include "bnj1185.mm"
include "pm2.61i.mm"
include "nfre1.mm"
include "19.9.mm"

theorem bnj1189
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  let vz: setvar z
  assume bnj1189.1: |- ( ph <-> ( R _FrSe A /\ B C_ A /\ B =/= (/) ) )
  assume bnj1189.2: |- ( ps <-> ( x e. B /\ y e. B /\ y R x ) )
  assume bnj1189.3: |- ( ch <-> A. y e. B -. y R x )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint R w
  disjoint R z
  assert |- ( ph -> E. x e. B A. y e. B -. y R x )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    vx
    wex
    @5
    wph
    wph
    @1
    cB
    wcel
    #
    wa
    #
    @5
    vx
    wph
    wph
    @6
    vx
    wex
    #
    wa
    @7
    vx
    wex
    wph
    @8
    cA
    cR
    w-bnj15
    cB
    cA
    wss
    cB
    c0
    wne
    #
    @8
    wph
    bnj1189.1
    @9
    @8
    vx
    cB
    n0
    biimpi
    bnj837
    ancli
    wph
    @6
    vx
    19.42v
    sylibr
    wch
    @7
    @5
    wi
    wch
    wph
    @6
    @5
    wph
    @6
    wch
    @5
    wph
    @6
    wch
    w3a
    #
    @6
    @4
    wa
    #
    vx
    wex
    #
    @5
    @10
    @11
    @12
    @10
    @6
    wch
    wa
    @11
    wph
    @6
    wch
    3simpc
    wch
    @4
    @6
    bnj1189.3
    anbi2i
    sylib
    @11
    vx
    19.8a
    syl
    @4
    vx
    cB
    df-rex
    sylibr
    3comr
    3expib
    wch
    wn
    #
    wph
    @6
    @5
    wph
    @6
    @13
    @5
    wph
    @6
    @13
    w3a
    #
    vx
    vy
    vw
    vz
    cB
    cR
    @14
    vz
    cv
    vw
    cv
    cR
    wbr
    wn
    vz
    cB
    wral
    vw
    cB
    wrex
    #
    vy
    @14
    wph
    wps
    wa
    #
    @15
    vy
    @14
    wph
    wps
    vy
    wex
    @16
    vy
    wex
    wph
    @6
    @13
    simp1
    @14
    @6
    @0
    cB
    wcel
    #
    @2
    w3a
    #
    vy
    wps
    @14
    @6
    @17
    @2
    wa
    #
    vy
    wex
    #
    @18
    vy
    wex
    #
    wph
    @6
    @13
    simp2
    @13
    wph
    @20
    @6
    @13
    @2
    vy
    cB
    @13
    @2
    vy
    cB
    wrex
    #
    @13
    @3
    wn
    #
    vy
    cB
    wrex
    #
    @22
    @4
    @24
    wch
    @24
    @4
    wn
    @3
    vy
    cB
    rexnal
    bicomi
    bnj1189.3
    xchnxbir
    @2
    @23
    vy
    cB
    @2
    notnotb
    rexbii
    bitr4i
    biimpi
    bnj1196
    3ad2ant3
    @21
    @6
    @19
    wa
    #
    vy
    wex
    @6
    @20
    wa
    @18
    @25
    vy
    @6
    @17
    @2
    3anass
    exbii
    @6
    @19
    vy
    19.42v
    bitri
    sylanbrc
    bnj1189.2
    bnj1198
    wph
    wps
    vy
    19.42v
    sylanbrc
    wph
    wps
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    bnj1189.1
    bnj1189.2
    bnj1190
    bnj593
    bnj937
    bnj1185
    3comr
    3expib
    pm2.61i
    bnj593
    @5
    vx
    @4
    vx
    cB
    nfre1
    19.9
    sylib
end
