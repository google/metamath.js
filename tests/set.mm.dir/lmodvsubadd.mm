include "clmod.mm"
include "wcel.mm"
include "cabl.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "lmodabl.mm"
include "ablsubadd.mm"
include "sylan.mm"

theorem lmodvsubadd
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume lmod4.v: |- V = ( Base ` W )
  assume lmod4.p: |- .+ = ( +g ` W )
  assume lmodvaddsub4.m: |- .- = ( -g ` W )


  assert |- ( ( W e. LMod /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( ( A .- B ) = C <-> ( B .+ C ) = A ) )

  proof
    cW
    clmod
    wcel
    cW
    cabl
    wcel
    cA
    cV
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    cA
    cB
    c.mi
    co
    cC
    wceq
    cB
    cC
    c.pl
    co
    cA
    wceq
    wb
    cW
    lmodabl
    cV
    c.pl
    cW
    c.mi
    cA
    cB
    cC
    lmod4.v
    lmod4.p
    lmodvaddsub4.m
    ablsubadd
    sylan
end
