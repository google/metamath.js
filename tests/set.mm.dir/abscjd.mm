include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cabs.mm"
include "wceq.mm"
include "abscj.mm"
include "syl.mm"

theorem abscjd
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( abs ` ( * ` A ) ) = ( abs ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cabs
    cfv
    cA
    cabs
    cfv
    wceq
    abscld.1
    cA
    abscj
    syl
end
