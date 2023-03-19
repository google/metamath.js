include "wceq.mm"
include "wcel.mm"
include "csuc.mm"
include "con0.mm"
include "sucidg.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "wn.mm"
include "word.mm"
include "suceloni.mm"
include "eqeltrd.mm"
include "eloni.mm"
include "ordirr.mm"
include "eleq1.mm"
include "biimprd.mm"
include "con3d.mm"
include "syl5com.mm"
include "mt2d.mm"
include "neqned.mm"

theorem sucneqond
  let wph: wff ph
  let cX: class X
  let cY: class Y
  assume sucneqond.1: |- ( ph -> X = suc Y )
  assume sucneqond.2: |- ( ph -> Y e. On )


  assert |- ( ph -> X =/= Y )

  proof
    wph
    cX
    cY
    wph
    cX
    cY
    wceq
    #
    cY
    cX
    wcel
    #
    wph
    cY
    cY
    csuc
    #
    cX
    wph
    cY
    con0
    wcel
    #
    cY
    @2
    wcel
    sucneqond.2
    cY
    con0
    sucidg
    syl
    sucneqond.1
    eleqtrrd
    wph
    cX
    cX
    wcel
    #
    wn
    #
    @0
    @1
    wn
    wph
    cX
    word
    #
    @5
    wph
    cX
    con0
    wcel
    @6
    wph
    cX
    @2
    con0
    sucneqond.1
    wph
    @3
    @2
    con0
    wcel
    sucneqond.2
    cY
    suceloni
    syl
    eqeltrd
    cX
    eloni
    syl
    cX
    ordirr
    syl
    @0
    @1
    @4
    @0
    @4
    @1
    cX
    cY
    cX
    eleq1
    biimprd
    con3d
    syl5com
    mt2d
    neqned
end
