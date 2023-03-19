include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "weu.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "ccat.mm"
include "cinito.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-inito.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem initoval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vh: setvar h
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume initoval.c: |- ( ph -> C e. Cat )
  assume initoval.b: |- B = ( Base ` C )
  assume initoval.h: |- H = ( Hom ` C )

  disjoint a b
  disjoint a h
  disjoint b h
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint C h
  disjoint a c
  disjoint b c
  disjoint c h
  disjoint B c
  disjoint C c
  disjoint H c
  disjoint c ph
  assert |- ( ph -> ( InitO ` C ) = { a e. B | A. b e. B E! h h e. ( a H b ) } )

  proof
    wph
    vc
    cC
    vh
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    chom
    cfv
    #
    co
    #
    wcel
    #
    vh
    weu
    #
    vb
    @3
    cbs
    cfv
    #
    wral
    #
    va
    @8
    crab
    #
    @0
    @1
    @2
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
    va
    cB
    crab
    #
    ccat
    cinito
    cvv
    cinito
    vc
    ccat
    @10
    cmpt
    wceq
    wph
    vh
    va
    vb
    vc
    df-inito
    a1i
    @3
    cC
    wceq
    #
    @10
    @15
    wceq
    wph
    @16
    @9
    @14
    va
    @8
    cB
    @16
    @8
    cC
    cbs
    cfv
    #
    cB
    @3
    cC
    cbs
    fveq2
    initoval.b
    syl6eqr
    #
    @16
    @7
    @13
    vb
    @8
    cB
    @18
    @16
    @6
    @12
    vh
    @16
    @5
    @11
    @0
    @16
    @4
    cH
    @1
    @2
    @16
    @4
    cC
    chom
    cfv
    cH
    @3
    cC
    chom
    fveq2
    initoval.h
    syl6eqr
    oveqd
    eleq2d
    eubidv
    raleqbidv
    rabeqbidv
    adantl
    initoval.c
    @15
    cvv
    wcel
    wph
    @14
    va
    cB
    cB
    @17
    cvv
    initoval.b
    cC
    cbs
    fvex
    eqeltri
    rabex
    a1i
    fvmptd
end
