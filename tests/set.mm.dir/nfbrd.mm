include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "nfopd.mm"
include "nfeld.mm"
include "nfxfrd.mm"

theorem nfbrd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume nfbrd.2: |- ( ph -> F/_ x A )
  assume nfbrd.3: |- ( ph -> F/_ x R )
  assume nfbrd.4: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/ x A R B )

  proof
    cA
    cB
    cR
    wbr
    cA
    cB
    cop
    #
    cR
    wcel
    wph
    vx
    cA
    cB
    cR
    df-br
    wph
    vx
    @0
    cR
    wph
    vx
    cA
    cB
    nfbrd.2
    nfbrd.4
    nfopd
    nfbrd.3
    nfeld
    nfxfrd
end
