include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "df-rmo.mm"
include "wnf.mm"
include "wtru.mm"
include "nftru.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfcvf.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfeld.mm"
include "nfand.mm"
include "adantl.mm"
include "nfmod2.mm"
include "trud.mm"
include "nfxfr.mm"

theorem nfrmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfreu.1: |- F/_ x A
  assume nfreu.2: |- F/ x ph


  assert |- F/ x E* y e. A ph

  proof
    wph
    vy
    cA
    wrmo
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
    wmo
    #
    vx
    wph
    vy
    cA
    df-rmo
    @3
    vx
    wnf
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
    @4
    vx
    @0
    cA
    vx
    vy
    nfcvf
    vx
    cA
    wnfc
    @4
    nfreu.1
    a1i
    nfeld
    wph
    vx
    wnf
    @4
    nfreu.2
    a1i
    nfand
    adantl
    nfmod2
    trud
    nfxfr
end
