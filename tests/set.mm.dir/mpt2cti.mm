include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cmpt2.mm"
include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "eqid.mm"
include "fnmpt2.mm"
include "ax-mp.mm"
include "xpct.mm"
include "fnct.mm"
include "sylancr.mm"

theorem mpt2cti
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume mpt2cti.1: |- A. x e. A A. y e. B C e. V

  disjoint B x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( ( A ~<_ _om /\ B ~<_ _om ) -> ( x e. A , y e. B |-> C ) ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    cB
    com
    cdom
    wbr
    wa
    vx
    vy
    cA
    cB
    cC
    cmpt2
    #
    cA
    cB
    cxp
    #
    wfn
    #
    @1
    com
    cdom
    wbr
    @0
    com
    cdom
    wbr
    cC
    cV
    wcel
    vy
    cB
    wral
    vx
    cA
    wral
    @2
    mpt2cti.1
    vx
    vy
    cA
    cB
    cC
    @0
    cV
    @0
    eqid
    fnmpt2
    ax-mp
    cA
    cB
    xpct
    @1
    @0
    fnct
    sylancr
end
