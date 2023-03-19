include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "simpl.mm"
include "cort.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "pjhth.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "pjpjpre.mm"

theorem axpjpj
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> A = ( ( ( projh ` H ) ` A ) +h ( ( projh ` ( _|_ ` H ) ) ` A ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    cA
    cH
    @0
    @1
    simpl
    @0
    cA
    cH
    cH
    cort
    cfv
    cph
    co
    #
    wcel
    @1
    @0
    @2
    chil
    cA
    cH
    pjhth
    eleq2d
    biimpar
    pjpjpre
end
