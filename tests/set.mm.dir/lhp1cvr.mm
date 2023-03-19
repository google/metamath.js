include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "islhp.mm"
include "simplbda.mm"

theorem lhp1cvr
  let cA: class A
  let cC: class C
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cW: class W
  assume lhp1cvr.u: |- .1. = ( 1. ` K )
  assume lhp1cvr.c: |- C = ( <o ` K )
  assume lhp1cvr.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. A /\ W e. H ) -> W C .1. )

  proof
    cK
    cA
    wcel
    cW
    cH
    wcel
    cW
    cK
    cbs
    cfv
    #
    wcel
    cW
    c.1
    cC
    wbr
    cA
    @0
    cC
    c.1
    cH
    cK
    cW
    @0
    eqid
    lhp1cvr.u
    lhp1cvr.c
    lhp1cvr.h
    islhp
    simplbda
end
