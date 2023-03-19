include "cop.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "cdm.mm"
include "wi.mm"
include "wceq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "spcegv.mm"
include "syl.mm"
include "wb.mm"
include "eldm2g.mm"
include "sylibrd.mm"

theorem opeldmd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vy: setvar y
  assume opeldmd.1: |- ( ph -> A e. V )
  assume opeldmd.2: |- ( ph -> B e. W )


  assert |- ( ph -> ( <. A , B >. e. C -> A e. dom C ) )

  proof
    wph
    cA
    cB
    cop
    #
    cC
    wcel
    #
    cA
    vy
    cv
    #
    cop
    #
    cC
    wcel
    #
    vy
    wex
    #
    cA
    cC
    cdm
    wcel
    #
    wph
    cB
    cW
    wcel
    @1
    @5
    wi
    opeldmd.2
    @4
    @1
    vy
    cB
    cW
    @2
    cB
    wceq
    @3
    @0
    cC
    @2
    cB
    cA
    opeq2
    eleq1d
    spcegv
    syl
    wph
    cA
    cV
    wcel
    @6
    @5
    wb
    opeldmd.1
    vy
    cA
    cC
    cV
    eldm2g
    syl
    sylibrd
end
