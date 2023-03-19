include "wcel.mm"
include "wbr.mm"
include "islhp.mm"
include "baibd.mm"

theorem islhp2
  let cA: class A
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  assume lhpset.b: |- B = ( Base ` K )
  assume lhpset.u: |- .1. = ( 1. ` K )
  assume lhpset.c: |- C = ( <o ` K )
  assume lhpset.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. A /\ W e. B ) -> ( W e. H <-> W C .1. ) )

  proof
    cK
    cA
    wcel
    cW
    cH
    wcel
    cW
    cB
    wcel
    cW
    c.1
    cC
    wbr
    cA
    cB
    cC
    c.1
    cH
    cK
    cW
    lhpset.b
    lhpset.u
    lhpset.c
    lhpset.h
    islhp
    baibd
end
