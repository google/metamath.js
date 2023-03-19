include "csalg.mm"
include "wcel.mm"
include "cuni.mm"
include "saluni.mm"
include "syl.mm"

theorem salunid
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let vx: setvar x
  assume salunid.1: |- ( ph -> S e. SAlg )


  assert |- ( ph -> U. S e. S )

  proof
    wph
    cS
    csalg
    wcel
    cS
    cuni
    cS
    wcel
    salunid.1
    cS
    saluni
    syl
end
