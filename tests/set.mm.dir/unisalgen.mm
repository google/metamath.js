include "cuni.mm"
include "salgenuni.mm"
include "eqcomd.mm"
include "csalg.mm"
include "wcel.mm"
include "csalgen.mm"
include "cfv.mm"
include "wceq.mm"
include "a1i.mm"
include "salgencl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "saluni.mm"

theorem unisalgen
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume unisalgen.x: |- ( ph -> X e. V )
  assume unisalgen.s: |- S = ( SalGen ` X )
  assume unisalgen.u: |- U = U. X


  assert |- ( ph -> U e. S )

  proof
    wph
    cU
    cS
    cuni
    #
    cS
    wph
    @0
    cU
    wph
    cS
    cU
    cV
    cX
    unisalgen.x
    unisalgen.s
    unisalgen.u
    salgenuni
    eqcomd
    wph
    cS
    csalg
    wcel
    @0
    cS
    wcel
    wph
    cS
    cX
    csalgen
    cfv
    #
    csalg
    cS
    @1
    wceq
    wph
    unisalgen.s
    a1i
    wph
    cX
    cV
    wcel
    @1
    csalg
    wcel
    unisalgen.x
    cV
    cX
    salgencl
    syl
    eqeltrd
    cS
    saluni
    syl
    eqeltrd
end
