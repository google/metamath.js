include "crab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-rab.mm"
include "sseq2i.mm"
include "ssab.mm"
include "dfss3.mm"
include "anbi1i.mm"
include "r19.26.mm"
include "df-ral.mm"
include "3bitr2ri.mm"
include "3bitri.mm"

theorem ssrab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( B C_ { x e. A | ph } <-> ( B C_ A /\ A. x e. B ph ) )

  proof
    cB
    wph
    vx
    cA
    crab
    #
    wss
    cB
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wss
    @1
    cB
    wcel
    @3
    wi
    vx
    wal
    #
    cB
    cA
    wss
    #
    wph
    vx
    cB
    wral
    #
    wa
    #
    @0
    @4
    cB
    wph
    vx
    cA
    df-rab
    sseq2i
    @3
    vx
    cB
    ssab
    @8
    @2
    vx
    cB
    wral
    #
    @7
    wa
    @3
    vx
    cB
    wral
    @5
    @6
    @9
    @7
    vx
    cB
    cA
    dfss3
    anbi1i
    @2
    wph
    vx
    cB
    r19.26
    @3
    vx
    cB
    df-ral
    3bitr2ri
    3bitri
end
