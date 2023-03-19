include "czeroo.mm"
include "cfv.mm"
include "wcel.mm"
include "cinito.mm"
include "ctermo.mm"
include "cin.mm"
include "wa.mm"
include "zerooval.mm"
include "eleq2d.mm"
include "elin.mm"
include "syl6bb.mm"

theorem iszeroo
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cI: class I
  let vb: setvar b
  let vi: setvar i
  let vh: setvar h
  assume isinito.b: |- B = ( Base ` C )
  assume isinito.h: |- H = ( Hom ` C )
  assume isinito.c: |- ( ph -> C e. Cat )
  assume isinito.i: |- ( ph -> I e. B )


  assert |- ( ph -> ( I e. ( ZeroO ` C ) <-> ( I e. ( InitO ` C ) /\ I e. ( TermO ` C ) ) ) )

  proof
    wph
    cI
    cC
    czeroo
    cfv
    #
    wcel
    cI
    cC
    cinito
    cfv
    #
    cC
    ctermo
    cfv
    #
    cin
    #
    wcel
    cI
    @1
    wcel
    cI
    @2
    wcel
    wa
    wph
    @0
    @3
    cI
    wph
    cB
    cC
    cH
    isinito.c
    isinito.b
    isinito.h
    zerooval
    eleq2d
    cI
    @1
    @2
    elin
    syl6bb
end
