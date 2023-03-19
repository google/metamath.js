include "cmoore.mm"
include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "cpw.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "elpwi.mm"
include "ex.mm"
include "syl5.mm"
include "alrimiv.mm"
include "df-ral.mm"
include "sylibr.mm"
include "wb.mm"
include "bj-ismoore.mm"
include "syl.mm"
include "mpbird.mm"

theorem bj-ismooredr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-ismooredr.1: |- ( ph -> A e. V )
  assume bj-ismooredr.2: |- ( ( ph /\ x C_ A ) -> ( U. A i^i |^| x ) e. A )

  disjoint ph x
  disjoint A x
  assert |- ( ph -> A e. Moore_ )

  proof
    wph
    cA
    cmoore
    wcel
    #
    cA
    cuni
    vx
    cv
    #
    cint
    cin
    cA
    wcel
    #
    vx
    cA
    cpw
    #
    wral
    #
    wph
    @1
    @3
    wcel
    #
    @2
    wi
    #
    vx
    wal
    @4
    wph
    @6
    vx
    @5
    @1
    cA
    wss
    #
    wph
    @2
    @1
    cA
    elpwi
    wph
    @7
    @2
    bj-ismooredr.2
    ex
    syl5
    alrimiv
    @2
    vx
    @3
    df-ral
    sylibr
    wph
    cA
    cV
    wcel
    @0
    @4
    wb
    bj-ismooredr.1
    vx
    cA
    cV
    bj-ismoore
    syl
    mpbird
end
