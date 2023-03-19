include "ctermo.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "weu.mm"
include "wral.mm"
include "crab.mm"
include "termoval.mm"
include "eleq2d.mm"
include "wb.mm"
include "wceq.mm"
include "oveq2.mm"
include "eubidv.mm"
include "ralbidv.mm"
include "elrab3.mm"
include "syl.mm"
include "bitrd.mm"

theorem istermo
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vh: setvar h
  let cH: class H
  let cI: class I
  let vb: setvar b
  let vi: setvar i
  assume isinito.b: |- B = ( Base ` C )
  assume isinito.h: |- H = ( Hom ` C )
  assume isinito.c: |- ( ph -> C e. Cat )
  assume isinito.i: |- ( ph -> I e. B )

  disjoint B b
  disjoint C b
  disjoint C h
  disjoint b h
  disjoint I b
  disjoint I h
  disjoint B i
  disjoint b i
  disjoint C i
  disjoint h i
  disjoint H i
  disjoint I i
  assert |- ( ph -> ( I e. ( TermO ` C ) <-> A. b e. B E! h h e. ( b H I ) ) )

  proof
    wph
    cI
    cC
    ctermo
    cfv
    #
    wcel
    cI
    vh
    cv
    #
    vb
    cv
    #
    vi
    cv
    #
    cH
    co
    #
    wcel
    #
    vh
    weu
    #
    vb
    cB
    wral
    #
    vi
    cB
    crab
    #
    wcel
    #
    @1
    @2
    cI
    cH
    co
    #
    wcel
    #
    vh
    weu
    #
    vb
    cB
    wral
    #
    wph
    @0
    @8
    cI
    wph
    cB
    cC
    vh
    cH
    vi
    vb
    isinito.c
    isinito.b
    isinito.h
    termoval
    eleq2d
    wph
    cI
    cB
    wcel
    @9
    @13
    wb
    isinito.i
    @7
    @13
    vi
    cI
    cB
    @3
    cI
    wceq
    #
    @6
    @12
    vb
    cB
    @14
    @5
    @11
    vh
    @14
    @4
    @10
    @1
    @3
    cI
    @2
    cH
    oveq2
    eleq2d
    eubidv
    ralbidv
    elrab3
    syl
    bitrd
end
