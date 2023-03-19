include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cim.mm"
include "caddc.mm"
include "cmul.mm"
include "ccj.mm"
include "recl.mm"
include "recnd.mm"
include "sqvald.mm"
include "imcl.mm"
include "oveq12d.mm"
include "wceq.mm"
include "ipcnval.mm"
include "anidms.mm"
include "cr.mm"
include "cjmulrcl.mm"
include "rere.mm"
include "syl.mm"
include "3eqtr2rd.mm"

theorem cjmulval
  let cA: class A


  assert |- ( A e. CC -> ( A x. ( * ` A ) ) = ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @1
    @1
    cmul
    co
    #
    @3
    @3
    cmul
    co
    #
    caddc
    co
    #
    cA
    cA
    ccj
    cfv
    cmul
    co
    #
    cre
    cfv
    #
    @8
    @0
    @2
    @5
    @4
    @6
    caddc
    @0
    @1
    @0
    @1
    cA
    recl
    recnd
    sqvald
    @0
    @3
    @0
    @3
    cA
    imcl
    recnd
    sqvald
    oveq12d
    @0
    @9
    @7
    wceq
    cA
    cA
    ipcnval
    anidms
    @0
    @8
    cr
    wcel
    @9
    @8
    wceq
    cA
    cjmulrcl
    @8
    rere
    syl
    3eqtr2rd
end
