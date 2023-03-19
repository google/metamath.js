include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "mulne0bd.mm"
include "mpbird.mm"
include "simprd.mm"

theorem mulne0bbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mulne0bad.1: |- ( ph -> A e. CC )
  assume mulne0bad.2: |- ( ph -> B e. CC )
  assume mulne0bad.3: |- ( ph -> ( A x. B ) =/= 0 )


  assert |- ( ph -> B =/= 0 )

  proof
    wph
    cA
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    wph
    @0
    @1
    wa
    cA
    cB
    cmul
    co
    cc0
    wne
    mulne0bad.3
    wph
    cA
    cB
    mulne0bad.1
    mulne0bad.2
    mulne0bd
    mpbird
    simprd
end
