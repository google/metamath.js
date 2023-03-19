include "cuni.mm"
include "cint.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "intssuni2.mm"
include "syl2anc.mm"
include "sseqin2.mm"
include "sylib.mm"
include "bj-ismoored.mm"
include "eqeltrrd.mm"

theorem bj-ismoored2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume bj-ismoored.1: |- ( ph -> A e. Moore_ )
  assume bj-ismoored.2: |- ( ph -> B C_ A )
  assume bj-ismoored2.3: |- ( ph -> B =/= (/) )


  assert |- ( ph -> |^| B e. A )

  proof
    wph
    cA
    cuni
    #
    cB
    cint
    #
    cin
    #
    @1
    cA
    wph
    @1
    @0
    wss
    #
    @2
    @1
    wceq
    wph
    cB
    cA
    wss
    cB
    c0
    wne
    @3
    bj-ismoored.2
    bj-ismoored2.3
    cB
    cA
    intssuni2
    syl2anc
    @1
    @0
    sseqin2
    sylib
    wph
    cA
    cB
    bj-ismoored.1
    bj-ismoored.2
    bj-ismoored
    eqeltrrd
end
