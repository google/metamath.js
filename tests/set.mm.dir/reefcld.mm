include "cr.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "reefcl.mm"
include "syl.mm"

theorem reefcld
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  assume reefcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( exp ` A ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    ce
    cfv
    cr
    wcel
    reefcld.1
    cA
    reefcl
    syl
end
