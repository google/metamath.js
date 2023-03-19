include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "cr.mm"
include "relogcl.mm"
include "syl.mm"

theorem relogcld
  let wph: wff ph
  let cA: class A
  assume relogcld.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( log ` A ) e. RR )

  proof
    wph
    cA
    crp
    wcel
    cA
    clog
    cfv
    cr
    wcel
    relogcld.1
    cA
    relogcl
    syl
end
