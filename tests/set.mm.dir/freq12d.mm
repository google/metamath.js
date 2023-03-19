include "wfr.mm"
include "wceq.mm"
include "wb.mm"
include "freq1.mm"
include "syl.mm"
include "freq2.mm"
include "bitrd.mm"

theorem freq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume weeq12d.l: |- ( ph -> R = S )
  assume weeq12d.r: |- ( ph -> A = B )


  assert |- ( ph -> ( R Fr A <-> S Fr B ) )

  proof
    wph
    cA
    cR
    wfr
    #
    cA
    cS
    wfr
    #
    cB
    cS
    wfr
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
    freq1
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
    freq2
    syl
    bitrd
end
