include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "isat.mm"
include "simplbda.mm"

theorem atcvr0
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cK: class K
  let c.0: class .0.
  assume atomcvr0.z: |- .0. = ( 0. ` K )
  assume atomcvr0.c: |- C = ( <o ` K )
  assume atomcvr0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. D /\ P e. A ) -> .0. C P )

  proof
    cK
    cD
    wcel
    cP
    cA
    wcel
    cP
    cK
    cbs
    cfv
    #
    wcel
    c.0
    cP
    cC
    wbr
    cA
    @0
    cC
    cD
    cP
    cK
    c.0
    @0
    eqid
    atomcvr0.z
    atomcvr0.c
    atomcvr0.a
    isat
    simplbda
end
