include "cid.mm"
include "cres.mm"
include "cv.mm"
include "wceq.mm"
include "eqidd.mm"
include "tendo0cbv.mm"
include "wfun.mm"
include "cvv.mm"
include "wcel.mm"
include "funi.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "fvmpt.mm"

theorem tendo02
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cK: class K
  let cO: class O
  let vg: setvar g
  assume tendo0cbv.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume tendo02.b: |- B = ( Base ` K )

  disjoint B f
  disjoint T f
  disjoint B g
  disjoint T g
  disjoint F g
  assert |- ( F e. T -> ( O ` F ) = ( _I |` B ) )

  proof
    vg
    cF
    cid
    cB
    cres
    #
    @0
    cT
    cO
    vg
    cv
    cF
    wceq
    @0
    eqidd
    cB
    cT
    vf
    vg
    cO
    tendo0cbv.o
    tendo0cbv
    cid
    wfun
    cB
    cvv
    wcel
    @0
    cvv
    wcel
    funi
    cB
    cK
    cbs
    cfv
    cvv
    tendo02.b
    cK
    cbs
    fvex
    eqeltri
    cid
    cB
    cvv
    resfunexg
    mp2an
    fvmpt
end
