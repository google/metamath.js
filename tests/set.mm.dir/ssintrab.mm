include "crab.mm"
include "cint.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wi.mm"
include "wral.mm"
include "df-rab.mm"
include "inteqi.mm"
include "sseq2i.mm"
include "wal.mm"
include "impexp.mm"
include "albii.mm"
include "ssintab.mm"
include "df-ral.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem ssintrab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( A C_ |^| { x e. B | ph } <-> A. x e. B ( ph -> A C_ x ) )

  proof
    cA
    wph
    vx
    cB
    crab
    #
    cint
    #
    wss
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    cint
    #
    wss
    #
    wph
    cA
    @2
    wss
    #
    wi
    #
    vx
    cB
    wral
    #
    @1
    @6
    cA
    @0
    @5
    wph
    vx
    cB
    df-rab
    inteqi
    sseq2i
    @4
    @8
    wi
    #
    vx
    wal
    @3
    @9
    wi
    #
    vx
    wal
    @7
    @10
    @11
    @12
    vx
    @3
    wph
    @8
    impexp
    albii
    @4
    vx
    cA
    ssintab
    @9
    vx
    cB
    df-ral
    3bitr4i
    bitri
end
