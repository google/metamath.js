include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cpw.mm"
include "elpwg.mm"
include "biimpar.mm"
include "syl2an.mm"

theorem elpwgded
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume elpwgded.1: |- ( ph -> A e. _V )
  assume elpwgded.2: |- ( ps -> A C_ B )


  assert |- ( ( ph /\ ps ) -> A e. ~P B )

  proof
    wph
    cA
    cvv
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cB
    cpw
    wcel
    #
    wps
    elpwgded.1
    elpwgded.2
    @0
    @2
    @1
    cA
    cB
    cvv
    elpwg
    biimpar
    syl2an
end
