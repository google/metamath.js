include "cr.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "clog.mm"
include "wceq.mm"
include "relogef.mm"
include "syl.mm"

theorem relogefd
  let wph: wff ph
  let cA: class A
  assume relogefd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( log ` ( exp ` A ) ) = A )

  proof
    wph
    cA
    cr
    wcel
    cA
    ce
    cfv
    clog
    cfv
    cA
    wceq
    relogefd.1
    cA
    relogef
    syl
end
