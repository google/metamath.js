include "cn.mm"
include "crab.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nnwof.mm"
include "ssrab2.mm"
include "biantrur.mm"
include "rabn0.mm"
include "bitr3i.mm"
include "wcel.mm"
include "wex.mm"
include "wal.mm"
include "df-rex.mm"
include "rabid.mm"
include "df-ral.mm"
include "elrab.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "albii.mm"
include "anbi12i.mm"
include "exbii.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "3imtr3i.mm"

theorem nnwos
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nnwos.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ( E. x e. NN ph -> E. x e. NN ( ph /\ A. y e. NN ( ps -> x <_ y ) ) )

  proof
    wph
    vx
    cn
    crab
    #
    cn
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @0
    wral
    #
    vx
    @0
    wrex
    #
    wph
    vx
    cn
    wrex
    #
    wph
    wps
    @6
    wi
    #
    vy
    cn
    wral
    #
    wa
    #
    vx
    cn
    wrex
    #
    vx
    vy
    @0
    wph
    vx
    cn
    nfrab1
    vy
    @0
    nfcv
    nnwof
    @3
    @2
    @9
    @1
    @2
    wph
    vx
    cn
    ssrab2
    biantrur
    wph
    vx
    cn
    rabn0
    bitr3i
    @8
    @4
    @0
    wcel
    #
    @7
    wa
    #
    vx
    wex
    @4
    cn
    wcel
    #
    wph
    wa
    #
    @5
    cn
    wcel
    #
    @10
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    wex
    #
    @13
    @7
    vx
    @0
    df-rex
    @15
    @21
    vx
    @14
    @17
    @7
    @20
    wph
    vx
    cn
    rabid
    @7
    @5
    @0
    wcel
    #
    @6
    wi
    #
    vy
    wal
    @20
    @6
    vy
    @0
    df-ral
    @24
    @19
    vy
    @24
    @18
    wps
    wa
    #
    @6
    wi
    @19
    @23
    @25
    @6
    wph
    wps
    vx
    @5
    cn
    nnwos.1
    elrab
    imbi1i
    @18
    wps
    @6
    impexp
    bitri
    albii
    bitri
    anbi12i
    exbii
    @22
    @16
    @12
    wa
    #
    vx
    wex
    @13
    @21
    @26
    vx
    @21
    @17
    @11
    wa
    @26
    @11
    @20
    @17
    @10
    vy
    cn
    df-ral
    anbi2i
    @16
    wph
    @11
    anass
    bitr3i
    exbii
    @12
    vx
    cn
    df-rex
    bitr4i
    3bitri
    3imtr3i
end
