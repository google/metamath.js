include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "ce.mm"
include "wceq.mm"
include "reeflog.mm"
include "syl.mm"

theorem reeflogd
  let wph: wff ph
  let cA: class A
  assume relogcld.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( exp ` ( log ` A ) ) = A )

  proof
    wph
    cA
    crp
    wcel
    cA
    clog
    cfv
    ce
    cfv
    cA
    wceq
    relogcld.1
    cA
    reeflog
    syl
end
