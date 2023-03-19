include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "nfeqd.mm"
include "nfnd.mm"
include "nfxfrd.mm"

theorem nfned
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfned.1: |- ( ph -> F/_ x A )
  assume nfned.2: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/ x A =/= B )

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    #
    wn
    wph
    vx
    cA
    cB
    df-ne
    wph
    @0
    vx
    wph
    vx
    cA
    cB
    nfned.1
    nfned.2
    nfeqd
    nfnd
    nfxfrd
end
