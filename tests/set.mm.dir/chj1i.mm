include "chil.mm"
include "chj.mm"
include "co.mm"
include "helch.mm"
include "chjcli.mm"
include "chssii.mm"
include "chub2i.mm"
include "eqssi.mm"

theorem chj1i
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH


  assert |- ( A vH ~H ) = ~H

  proof
    cA
    chil
    chj
    co
    #
    chil
    @0
    cA
    chil
    ch0le.1
    helch
    chjcli
    chssii
    chil
    cA
    helch
    ch0le.1
    chub2i
    eqssi
end
