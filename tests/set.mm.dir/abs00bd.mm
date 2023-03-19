include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "abs00ad.mm"
include "mpbird.mm"

theorem abs00bd
  let wph: wff ph
  let cA: class A
  assume abs00bd.1: |- ( ph -> A = 0 )


  assert |- ( ph -> ( abs ` A ) = 0 )

  proof
    wph
    cA
    cabs
    cfv
    cc0
    wceq
    cA
    cc0
    wceq
    abs00bd.1
    wph
    cA
    wph
    cA
    cc0
    cc
    abs00bd.1
    0cn
    syl6eqel
    abs00ad
    mpbird
end
