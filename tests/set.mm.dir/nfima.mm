include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "nfres.mm"
include "nfrn.mm"
include "nfcxfr.mm"

theorem nfima
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfima.1: |- F/_ x A
  assume nfima.2: |- F/_ x B


  assert |- F/_ x ( A " B )

  proof
    vx
    cA
    cB
    cima
    cA
    cB
    cres
    #
    crn
    cA
    cB
    df-ima
    vx
    @0
    vx
    cA
    cB
    nfima.1
    nfima.2
    nfres
    nfrn
    nfcxfr
end
