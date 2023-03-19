include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "cab.mm"
include "wral.mm"
include "crab.mm"
include "wsbc.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nfv.mm"
include "nfral.mm"
include "weq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "cbvrab.mm"
include "df-rab.mm"
include "abid.mm"
include "df-ral.mm"
include "df-sbc.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitr4i.mm"
include "anbi12i.mm"
include "abbii.mm"
include "3eqtri.mm"
include "scottex.mm"
include "eqeltrri.mm"

theorem scottexs
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- { x | ( ph /\ A. y ( [. y / x ]. ph -> ( rank ` x ) C_ ( rank ` y ) ) ) } e. _V

  proof
    vz
    cv
    #
    crnk
    cfv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    wss
    #
    vy
    wph
    vx
    cab
    #
    wral
    #
    vz
    @5
    crab
    #
    wph
    wph
    vx
    @2
    wsbc
    #
    vx
    cv
    #
    crnk
    cfv
    #
    @3
    wss
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    cab
    #
    cvv
    @7
    @11
    vy
    @5
    wral
    #
    vx
    @5
    crab
    @9
    @5
    wcel
    #
    @16
    wa
    #
    vx
    cab
    @15
    @6
    @16
    vz
    vx
    @5
    vz
    @5
    nfcv
    wph
    vx
    nfab1
    #
    @4
    vx
    vy
    @5
    @19
    @4
    vx
    nfv
    nfral
    @16
    vz
    nfv
    vz
    vx
    weq
    #
    @4
    @11
    vy
    @5
    @20
    @1
    @10
    @3
    @0
    @9
    crnk
    fveq2
    sseq1d
    ralbidv
    cbvrab
    @16
    vx
    @5
    df-rab
    @18
    @14
    vx
    @17
    wph
    @16
    @13
    wph
    vx
    abid
    @16
    @2
    @5
    wcel
    #
    @11
    wi
    #
    vy
    wal
    @13
    @11
    vy
    @5
    df-ral
    @12
    @22
    vy
    @8
    @21
    @11
    wph
    vx
    @2
    df-sbc
    imbi1i
    albii
    bitr4i
    anbi12i
    abbii
    3eqtri
    vz
    vy
    @5
    scottex
    eqeltrri
end
