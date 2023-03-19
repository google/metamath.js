include "chj.mm"
include "co.mm"
include "chub1i.mm"
include "chjcomi.mm"
include "sseqtri.mm"

theorem chub2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- A C_ ( B vH A )

  proof
    cA
    cA
    cB
    chj
    co
    cB
    cA
    chj
    co
    cA
    cB
    ch0le.1
    chjcl.2
    chub1i
    cA
    cB
    ch0le.1
    chjcl.2
    chjcomi
    sseqtri
end
