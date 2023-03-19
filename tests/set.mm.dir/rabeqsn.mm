include "crab.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wb.mm"
include "wal.mm"
include "df-rab.mm"
include "df-sn.mm"
include "eqeq12i.mm"
include "abbi.mm"
include "bitr4i.mm"

theorem rabeqsn
  let wph: wff ph
  let vx: setvar x
  let cV: class V
  let cX: class X

  disjoint X x
  assert |- ( { x e. V | ph } = { X } <-> A. x ( ( x e. V /\ ph ) <-> x = X ) )

  proof
    wph
    vx
    cV
    crab
    #
    cX
    csn
    #
    wceq
    vx
    cv
    #
    cV
    wcel
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
    wceq
    @3
    @5
    wb
    vx
    wal
    @0
    @4
    @1
    @6
    wph
    vx
    cV
    df-rab
    vx
    cX
    df-sn
    eqeq12i
    @3
    @5
    vx
    abbi
    bitr4i
end
