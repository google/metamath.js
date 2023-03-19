include "wwe.mm"
include "wceq.mm"
include "wb.mm"
include "weeq1.mm"
include "syl.mm"
include "weeq2.mm"
include "bitrd.mm"

theorem weeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume weeq12d.l: |- ( ph -> R = S )
  assume weeq12d.r: |- ( ph -> A = B )


  assert |- ( ph -> ( R We A <-> S We B ) )

  proof
    wph
    cA
    cR
    wwe
    #
    cA
    cS
    wwe
    #
    cB
    cS
    wwe
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
    weeq1
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
    weeq2
    syl
    bitrd
end
