include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "wceq.mm"
include "absvalsq2.mm"
include "syl.mm"

theorem absvalsq2d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( abs ` A ) ^ 2 ) = ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) )

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
    cre
    cfv
    c2
    cexp
    co
    cA
    cim
    cfv
    c2
    cexp
    co
    caddc
    co
    wceq
    abscld.1
    cA
    absvalsq2
    syl
end
