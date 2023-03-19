include "csalgen.mm"
include "cfv.mm"
include "csalg.mm"
include "wcel.mm"
include "salgencl.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem salgencld
  let wph: wff ph
  let cS: class S
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume salgencld.1: |- ( ph -> X e. V )
  assume salgencld.2: |- S = ( SalGen ` X )


  assert |- ( ph -> S e. SAlg )

  proof
    wph
    cS
    cX
    csalgen
    cfv
    #
    csalg
    salgencld.2
    wph
    cX
    cV
    wcel
    @0
    csalg
    wcel
    salgencld.1
    cV
    cX
    salgencl
    syl
    syl5eqel
end
