include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "eqeltrrd.mm"
include "subeq0ad.mm"
include "mpbird.mm"

theorem subeq0bd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume subeq0bd.1: |- ( ph -> A e. CC )
  assume subeq0bd.2: |- ( ph -> A = B )


  assert |- ( ph -> ( A - B ) = 0 )

  proof
    wph
    cA
    cB
    cmin
    co
    cc0
    wceq
    cA
    cB
    wceq
    subeq0bd.2
    wph
    cA
    cB
    subeq0bd.1
    wph
    cA
    cB
    cc
    subeq0bd.2
    subeq0bd.1
    eqeltrrd
    subeq0ad
    mpbird
end
