include "wor.mm"
include "wceq.mm"
include "wb.mm"
include "soeq1.mm"
include "syl.mm"
include "soeq2.mm"
include "bitrd.mm"

theorem soeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume weeq12d.l: |- ( ph -> R = S )
  assume weeq12d.r: |- ( ph -> A = B )


  assert |- ( ph -> ( R Or A <-> S Or B ) )

  proof
    wph
    cA
    cR
    wor
    #
    cA
    cS
    wor
    #
    cB
    cS
    wor
    #
    wph
    cR
    cS
    wceq
    @0
    @1
    wb
    weeq12d.l
    cA
    cR
    cS
    soeq1
    syl
    wph
    cA
    cB
    wceq
    @1
    @2
    wb
    weeq12d.r
    cA
    cB
    cS
    soeq2
    syl
    bitrd
end
