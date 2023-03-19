include "cle.mm"
include "breqtrd.mm"

theorem leeq2d
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  assume leeq2d.1: |- ( ph -> A <_ C )
  assume leeq2d.2: |- ( ph -> C = D )
  assume leeq2d.3: |- ( ph -> A e. RR )
  assume leeq2d.4: |- ( ph -> C e. RR )


  assert |- ( ph -> A <_ D )

  proof
    wph
    cA
    cC
    cD
    cle
    leeq2d.1
    leeq2d.2
    breqtrd
end
