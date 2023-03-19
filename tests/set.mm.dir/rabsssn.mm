include "crab.mm"
include "csn.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-rab.mm"
include "df-sn.mm"
include "sseq12i.mm"
include "ss2ab.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem rabsssn
  let wph: wff ph
  let vx: setvar x
  let cV: class V
  let cX: class X

  disjoint X x
  assert |- ( { x e. V | ph } C_ { X } <-> A. x e. V ( ph -> x = X ) )

  proof
    wph
    vx
    cV
    crab
    #
    cX
    csn
    #
    wss
    vx
    cv
    #
    cV
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @2
    cX
    wceq
    #
    vx
    cab
    #
    wss
    @4
    @6
    wi
    #
    vx
    wal
    #
    wph
    @6
    wi
    #
    vx
    cV
    wral
    #
    @0
    @5
    @1
    @7
    wph
    vx
    cV
    df-rab
    vx
    cX
    df-sn
    sseq12i
    @4
    @6
    vx
    ss2ab
    @9
    @3
    @10
    wi
    #
    vx
    wal
    @11
    @8
    @12
    vx
    @3
    wph
    @6
    impexp
    albii
    @10
    vx
    cV
    df-ral
    bitr4i
    3bitri
end
