include "wbr.mm"
include "breq2d.mm"
include "mpbid.mm"

theorem breqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breqtrd.1: |- ( ph -> A R B )
  assume breqtrd.2: |- ( ph -> B = C )


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cR
    wbr
    cA
    cC
    cR
    wbr
    breqtrd.1
    wph
    cB
    cC
    cA
    cR
    breqtrd.2
    breq2d
    mpbid
end
