include "cr.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "crp.mm"
include "rpefcl.mm"
include "syl.mm"

theorem rpefcld
  let wph: wff ph
  let cA: class A
  assume rpefcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( exp ` A ) e. RR+ )

  proof
    wph
    cA
    cr
    wcel
    cA
    ce
    cfv
    crp
    wcel
    rpefcld.1
    cA
    rpefcl
    syl
end
