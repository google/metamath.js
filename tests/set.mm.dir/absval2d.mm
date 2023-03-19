include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cre.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cim.mm"
include "caddc.mm"
include "csqrt.mm"
include "wceq.mm"
include "absval2.mm"
include "syl.mm"

theorem absval2d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( abs ` A ) = ( sqrt ` ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cabs
    cfv
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
    csqrt
    cfv
    wceq
    abscld.1
    cA
    absval2
    syl
end
