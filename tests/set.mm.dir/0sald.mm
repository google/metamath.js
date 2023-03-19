include "csalg.mm"
include "wcel.mm"
include "c0.mm"
include "0sal.mm"
include "syl.mm"

theorem 0sald
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let vx: setvar x
  assume 0sald.1: |- ( ph -> S e. SAlg )


  assert |- ( ph -> (/) e. S )

  proof
    wph
    cS
    csalg
    wcel
    c0
    cS
    wcel
    0sald.1
    cS
    0sal
    syl
end
