include "wbr.mm"
include "breq12d.mm"
include "breqd.mm"
include "bitrd.mm"

theorem breq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume breq1d.1: |- ( ph -> A = B )
  assume breq123d.2: |- ( ph -> R = S )
  assume breq123d.3: |- ( ph -> C = D )


  assert |- ( ph -> ( A R C <-> B S D ) )

  proof
    wph
    cA
    cC
    cR
    wbr
    cB
    cD
    cR
    wbr
    cB
    cD
    cS
    wbr
    wph
    cA
    cB
    cC
    cD
    cR
    breq1d.1
    breq123d.3
    breq12d
    wph
    cR
    cS
    cB
    cD
    breq123d.2
    breqd
    bitrd
end
