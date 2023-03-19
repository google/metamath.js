include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cima.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "wf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseqr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"

theorem wnefimgd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume wnefimgd.1: |- ( ph -> A =/= (/) )
  assume wnefimgd.2: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( F " A ) =/= (/) )

  proof
    wph
    cF
    cdm
    #
    cA
    cin
    #
    c0
    wne
    cF
    cA
    cima
    #
    c0
    wne
    wph
    @1
    cA
    c0
    wph
    cA
    @0
    wss
    @1
    cA
    wceq
    wph
    cA
    cA
    @0
    cA
    ssid
    wph
    cA
    cB
    cF
    wf
    @0
    cA
    wceq
    wnefimgd.2
    cA
    cB
    cF
    fdm
    syl
    syl5sseqr
    cA
    @0
    sseqin2
    sylib
    wnefimgd.1
    eqnetrd
    @2
    c0
    @1
    c0
    cF
    cA
    imadisj
    necon3bii
    sylibr
end
