include "wbr.mm"
include "breq2d.mm"
include "mtbid.mm"

theorem brneqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume brneqtrd.1: |- ( ph -> -. A R B )
  assume brneqtrd.2: |- ( ph -> B = C )


  assert |- ( ph -> -. A R C )

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
    brneqtrd.1
    wph
    cB
    cC
    cA
    cR
    brneqtrd.2
    breq2d
    mtbid
end
