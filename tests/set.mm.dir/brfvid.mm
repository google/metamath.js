include "cid.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "syl.mm"
include "breqd.mm"

theorem brfvid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  assume brfvid.r: |- ( ph -> R e. _V )


  assert |- ( ph -> ( A ( _I ` R ) B <-> A R B ) )

  proof
    wph
    cR
    cid
    cfv
    #
    cR
    cA
    cB
    wph
    cR
    cvv
    wcel
    @0
    cR
    wceq
    brfvid.r
    cR
    cvv
    fvi
    syl
    breqd
end
