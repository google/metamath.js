include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "wnfc.mm"
include "wtru.mm"
include "nftru.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnf.mm"
include "nfcri.mm"
include "eleq1.mm"
include "dvelimnf.mm"
include "a1i.mm"
include "nfand.mm"
include "adantl.mm"
include "nfabd2.mm"
include "trud.mm"
include "nfcxfr.mm"

theorem nfrab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume nfrab.1: |- F/ x ph
  assume nfrab.2: |- F/_ x A


  assert |- F/_ x { y e. A | ph }

  proof
    vx
    wph
    vy
    cA
    crab
    vy
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vy
    cab
    #
    wph
    vy
    cA
    df-rab
    vx
    @3
    wnfc
    wtru
    @2
    vx
    vy
    vy
    nftru
    vx
    vy
    weq
    vx
    wal
    wn
    #
    @2
    vx
    wnf
    wtru
    @4
    @1
    wph
    vx
    vz
    cv
    #
    cA
    wcel
    @1
    vx
    vy
    vz
    vx
    vz
    cA
    nfrab.2
    nfcri
    @5
    @0
    cA
    eleq1
    dvelimnf
    wph
    vx
    wnf
    @4
    nfrab.1
    a1i
    nfand
    adantl
    nfabd2
    trud
    nfcxfr
end
