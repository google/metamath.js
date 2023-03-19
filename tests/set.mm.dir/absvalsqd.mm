include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
include "cmul.mm"
include "wceq.mm"
include "absvalsq.mm"
include "syl.mm"

theorem absvalsqd
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( abs ` A ) ^ 2 ) = ( A x. ( * ` A ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cabs
    cfv
    c2
    cexp
    co
    cA
    cA
    ccj
    cfv
    cmul
    co
    wceq
    abscld.1
    cA
    absvalsq
    syl
end
