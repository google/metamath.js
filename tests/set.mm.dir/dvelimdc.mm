include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnfc.mm"
include "wa.mm"
include "nfv.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "nfcrd.mm"
include "wceq.mm"
include "wb.mm"
include "eleq2.mm"
include "syl6.mm"
include "dvelimdf.mm"
include "imp.mm"
include "nfcd.mm"
include "ex.mm"

theorem dvelimdc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume dvelimdc.1: |- F/ x ph
  assume dvelimdc.2: |- F/ z ph
  assume dvelimdc.3: |- ( ph -> F/_ x A )
  assume dvelimdc.4: |- ( ph -> F/_ z B )
  assume dvelimdc.5: |- ( ph -> ( z = y -> A = B ) )


  assert |- ( ph -> ( -. A. x x = y -> F/_ x B ) )

  proof
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    #
    vx
    cB
    wnfc
    wph
    @0
    wa
    #
    vx
    vw
    cB
    @1
    vw
    nfv
    wph
    @0
    vw
    cv
    #
    cB
    wcel
    #
    vx
    wnf
    wph
    @2
    cA
    wcel
    #
    @3
    vx
    vy
    vz
    dvelimdc.1
    dvelimdc.2
    wph
    vx
    vw
    cA
    dvelimdc.3
    nfcrd
    wph
    vz
    vw
    cB
    dvelimdc.4
    nfcrd
    wph
    vz
    vy
    weq
    cA
    cB
    wceq
    @4
    @3
    wb
    dvelimdc.5
    cA
    cB
    @2
    eleq2
    syl6
    dvelimdf
    imp
    nfcd
    ex
end
