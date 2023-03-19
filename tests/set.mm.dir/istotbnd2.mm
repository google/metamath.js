include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cfn.mm"
include "crp.mm"
include "istotbnd.mm"
include "baib.mm"

theorem istotbnd2
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vd: setvar d

  disjoint M d
  disjoint M v
  disjoint M b
  disjoint M x
  disjoint d v
  disjoint b d
  disjoint d x
  disjoint b v
  disjoint v x
  disjoint b x
  disjoint X d
  disjoint X v
  disjoint X b
  disjoint X x
  assert |- ( M e. ( Met ` X ) -> ( M e. ( TotBnd ` X ) <-> A. d e. RR+ E. v e. Fin ( U. v = X /\ A. b e. v E. x e. X b = ( x ( ball ` M ) d ) ) ) )

  proof
    cM
    cX
    ctotbnd
    cfv
    wcel
    cM
    cX
    cme
    cfv
    wcel
    vv
    cv
    #
    cuni
    cX
    wceq
    vb
    cv
    vx
    cv
    vd
    cv
    cM
    cbl
    cfv
    co
    wceq
    vx
    cX
    wrex
    vb
    @0
    wral
    wa
    vv
    cfn
    wrex
    vd
    crp
    wral
    vx
    vv
    cM
    cX
    vb
    vd
    istotbnd
    baib
end
