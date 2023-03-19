include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "df-nel.mm"
include "nfeld.mm"
include "nfnd.mm"
include "nfxfrd.mm"

theorem nfneld
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfneld.1: |- ( ph -> F/_ x A )
  assume nfneld.2: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/ x A e/ B )

  proof
    cA
    cB
    wnel
    cA
    cB
    wcel
    #
    wn
    wph
    vx
    cA
    cB
    df-nel
    wph
    @0
    vx
    wph
    vx
    cA
    cB
    nfneld.1
    nfneld.2
    nfeld
    nfnd
    nfxfrd
end
