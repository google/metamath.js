include "cvv.mm"
include "wcel.mm"
include "c1.mm"
include "crelexp.mm"
include "co.mm"
include "wceq.mm"
include "relexp1g.mm"
include "syl.mm"

theorem relexp1d
  let wph: wff ph
  let cR: class R
  assume relexp1d.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( R ^r 1 ) = R )

  proof
    wph
    cR
    cvv
    wcel
    cR
    c1
    crelexp
    co
    cR
    wceq
    relexp1d.2
    cR
    cvv
    relexp1g
    syl
end
