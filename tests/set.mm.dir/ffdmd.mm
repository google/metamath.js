include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "ffdm.mm"
include "syl.mm"
include "simpld.mm"

theorem ffdmd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume ffdmd.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> F : dom F --> B )

  proof
    wph
    cF
    cdm
    #
    cB
    cF
    wf
    #
    @0
    cA
    wss
    #
    wph
    cA
    cB
    cF
    wf
    @1
    @2
    wa
    ffdmd.1
    cA
    cB
    cF
    ffdm
    syl
    simpld
end
