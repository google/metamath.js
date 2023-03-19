include "clmod.mm"
include "wcel.mm"
include "cabl.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "lmodabl.mm"
include "abladdsub4.mm"
include "syl3an1.mm"

theorem lmodvaddsub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume lmod4.v: |- V = ( Base ` W )
  assume lmod4.p: |- .+ = ( +g ` W )
  assume lmodvaddsub4.m: |- .- = ( -g ` W )


  assert |- ( ( W e. LMod /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( A .+ B ) = ( C .+ D ) <-> ( A .- C ) = ( D .- B ) ) )

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
    wa
    cC
    cV
    wcel
    cD
    cV
    wcel
    wa
    cA
    cB
    c.pl
    co
    cC
    cD
    c.pl
    co
    wceq
    cA
    cC
    c.mi
    co
    cD
    cB
    c.mi
    co
    wceq
    wb
    cW
    lmodabl
    cV
    c.pl
    cW
    c.mi
    cD
    cA
    cB
    cC
    lmod4.v
    lmod4.p
    lmodvaddsub4.m
    abladdsub4
    syl3an1
end
