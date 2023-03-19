include "wcel.mm"
include "ctskm.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "ctsk.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "tskmval.mm"
include "df-rab.mm"
include "inteqi.mm"
include "syl6eq.mm"
include "sseq2d.mm"
include "wal.mm"
include "impexp.mm"
include "albii.mm"
include "ssintab.mm"
include "df-ral.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem sstskm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( B C_ ( tarskiMap ` A ) <-> A. x e. Tarski ( A e. x -> B C_ x ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    ctskm
    cfv
    #
    wss
    cB
    vx
    cv
    #
    ctsk
    wcel
    #
    cA
    @2
    wcel
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    wss
    #
    @4
    cB
    @2
    wss
    #
    wi
    #
    vx
    ctsk
    wral
    #
    @0
    @1
    @7
    cB
    @0
    @1
    @4
    vx
    ctsk
    crab
    #
    cint
    @7
    vx
    cA
    cV
    tskmval
    @12
    @6
    @4
    vx
    ctsk
    df-rab
    inteqi
    syl6eq
    sseq2d
    @5
    @9
    wi
    #
    vx
    wal
    @3
    @10
    wi
    #
    vx
    wal
    @8
    @11
    @13
    @14
    vx
    @3
    @4
    @9
    impexp
    albii
    @5
    vx
    cB
    ssintab
    @10
    vx
    ctsk
    df-ral
    3bitr4i
    syl6bb
end
