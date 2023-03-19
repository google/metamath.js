include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "wceq.mm"
include "ancrb.mm"
include "albii.mm"
include "nfv.mm"
include "nfsab1.mm"
include "nfrab1.mm"
include "nfcri.mm"
include "nfim.mm"
include "weq.mm"
include "abid.mm"
include "eleq1.mm"
include "syl5bbr.mm"
include "rabid.mm"
include "imbi12d.mm"
include "cbval.mm"
include "wss.mm"
include "eqss.mm"
include "rabssab.mm"
include "biantrur.mm"
include "dfss2.mm"
include "3bitr2ri.mm"
include "3bitri.mm"

theorem rababg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- ( A. x ( ph -> x e. A ) <-> { x e. A | ph } = { x | ph } )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wi
    #
    vx
    wal
    wph
    @1
    wph
    wa
    #
    wi
    #
    vx
    wal
    vy
    cv
    #
    wph
    vx
    cab
    #
    wcel
    #
    @5
    wph
    vx
    cA
    crab
    #
    wcel
    #
    wi
    #
    vy
    wal
    #
    @8
    @6
    wceq
    #
    @2
    @4
    vx
    wph
    @1
    ancrb
    albii
    @4
    @10
    vx
    vy
    @4
    vy
    nfv
    @7
    @9
    vx
    wph
    vx
    vy
    nfsab1
    vx
    vy
    @8
    wph
    vx
    cA
    nfrab1
    nfcri
    nfim
    vx
    vy
    weq
    #
    wph
    @7
    @3
    @9
    wph
    @0
    @6
    wcel
    @13
    @7
    wph
    vx
    abid
    @0
    @5
    @6
    eleq1
    syl5bbr
    @3
    @0
    @8
    wcel
    @13
    @9
    wph
    vx
    cA
    rabid
    @0
    @5
    @8
    eleq1
    syl5bbr
    imbi12d
    cbval
    @12
    @8
    @6
    wss
    #
    @6
    @8
    wss
    #
    wa
    @15
    @11
    @8
    @6
    eqss
    @14
    @15
    wph
    vx
    cA
    rabssab
    biantrur
    vy
    @6
    @8
    dfss2
    3bitr2ri
    3bitri
end
