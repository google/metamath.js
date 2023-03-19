include "co.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "nfopd.mm"
include "nffvd.mm"
include "nfcxfrd.mm"

theorem nfovd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume nfovd.2: |- ( ph -> F/_ x A )
  assume nfovd.3: |- ( ph -> F/_ x F )
  assume nfovd.4: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x ( A F B ) )

  proof
    wph
    vx
    cA
    cB
    cF
    co
    cA
    cB
    cop
    #
    cF
    cfv
    cA
    cB
    cF
    df-ov
    wph
    vx
    @0
    cF
    nfovd.3
    wph
    vx
    cA
    cB
    nfovd.2
    nfovd.4
    nfopd
    nffvd
    nfcxfrd
end
