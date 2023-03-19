include "wex.mm"
include "cab.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wsbc.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "abn0.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "scott0.mm"
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
include "eqeq1i.mm"
include "bitri.mm"
include "necon3bii.mm"
include "bitr3i.mm"

theorem scott0s
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( E. x ph <-> { x | ( ph /\ A. y ( [. y / x ]. ph -> ( rank ` x ) C_ ( rank ` y ) ) ) } =/= (/) )

  proof
    wph
    vx
    wex
    wph
    vx
    cab
    #
    c0
    wne
    wph
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    vx
    cv
    #
    crnk
    cfv
    #
    @1
    crnk
    cfv
    #
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
    c0
    wne
    wph
    vx
    abn0
    @0
    c0
    @10
    c0
    @0
    c0
    wceq
    vz
    cv
    #
    crnk
    cfv
    #
    @5
    wss
    #
    vy
    @0
    wral
    #
    vz
    @0
    crab
    #
    c0
    wceq
    @10
    c0
    wceq
    vz
    vy
    @0
    scott0
    @15
    @10
    c0
    @15
    @6
    vy
    @0
    wral
    #
    vx
    @0
    crab
    @3
    @0
    wcel
    #
    @16
    wa
    #
    vx
    cab
    @10
    @14
    @16
    vz
    vx
    @0
    vz
    @0
    nfcv
    wph
    vx
    nfab1
    #
    @13
    vx
    vy
    @0
    @19
    @13
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
    @13
    @6
    vy
    @0
    @20
    @12
    @4
    @5
    @11
    @3
    crnk
    fveq2
    sseq1d
    ralbidv
    cbvrab
    @16
    vx
    @0
    df-rab
    @18
    @9
    vx
    @17
    wph
    @16
    @8
    wph
    vx
    abid
    @16
    @1
    @0
    wcel
    #
    @6
    wi
    #
    vy
    wal
    @8
    @6
    vy
    @0
    df-ral
    @7
    @22
    vy
    @2
    @21
    @6
    wph
    vx
    @1
    df-sbc
    imbi1i
    albii
    bitr4i
    anbi12i
    abbii
    3eqtri
    eqeq1i
    bitri
    necon3bii
    bitr3i
end
