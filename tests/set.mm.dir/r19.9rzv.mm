include "wrex.mm"
include "wn.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "dfrex2.mm"
include "r19.3rzv.mm"
include "con1bid.mm"
include "syl5rbb.mm"

theorem r19.9rzv
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ph x
  assert |- ( A =/= (/) -> ( ph <-> E. x e. A ph ) )

  proof
    wph
    vx
    cA
    wrex
    wph
    wn
    #
    vx
    cA
    wral
    #
    wn
    cA
    c0
    wne
    #
    wph
    wph
    vx
    cA
    dfrex2
    @2
    wph
    @1
    @0
    vx
    cA
    r19.3rzv
    con1bid
    syl5rbb
end
