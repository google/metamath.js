include "cle.mm"
include "eqbrtrrd.mm"

theorem leeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leeq1d.1: |- ( ph -> A <_ C )
  assume leeq1d.2: |- ( ph -> A = B )
  assume leeq1d.3: |- ( ph -> A e. RR )
  assume leeq1d.4: |- ( ph -> C e. RR )


  assert |- ( ph -> B <_ C )

  proof
    wph
    cA
    cB
    cC
    cle
    leeq1d.2
    leeq1d.1
    eqbrtrrd
end
