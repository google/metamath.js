include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cim.mm"
include "cmin.mm"
include "cneg.mm"
include "caddc.mm"
include "wceq.mm"
include "cjcl.mm"
include "remul.mm"
include "sylan2.mm"
include "recj.mm"
include "adantl.mm"
include "oveq2d.mm"
include "imcj.mm"
include "imcl.mm"
include "recnd.mm"
include "mulneg2.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "recl.mm"
include "mulcl.mm"
include "subnegd.mm"
include "3eqtrd.mm"

theorem ipcnval
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( Re ` ( A x. ( * ` B ) ) ) = ( ( ( Re ` A ) x. ( Re ` B ) ) + ( ( Im ` A ) x. ( Im ` B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    ccj
    cfv
    #
    cmul
    co
    cre
    cfv
    #
    cA
    cre
    cfv
    #
    @3
    cre
    cfv
    #
    cmul
    co
    #
    cA
    cim
    cfv
    #
    @3
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @5
    cB
    cre
    cfv
    #
    cmul
    co
    #
    @8
    cB
    cim
    cfv
    #
    cmul
    co
    #
    cneg
    #
    cmin
    co
    @13
    @15
    caddc
    co
    @1
    @0
    @3
    cc
    wcel
    @4
    @11
    wceq
    cB
    cjcl
    cA
    @3
    remul
    sylan2
    @2
    @7
    @13
    @10
    @16
    cmin
    @2
    @6
    @12
    @5
    cmul
    @1
    @6
    @12
    wceq
    @0
    cB
    recj
    adantl
    oveq2d
    @2
    @10
    @8
    @14
    cneg
    #
    cmul
    co
    #
    @16
    @2
    @9
    @17
    @8
    cmul
    @1
    @9
    @17
    wceq
    @0
    cB
    imcj
    adantl
    oveq2d
    @0
    @8
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @18
    @16
    wceq
    @1
    @0
    @8
    cA
    imcl
    recnd
    #
    @1
    @14
    cB
    imcl
    recnd
    #
    @8
    @14
    mulneg2
    syl2an
    eqtrd
    oveq12d
    @2
    @13
    @15
    @0
    @5
    cc
    wcel
    @12
    cc
    wcel
    @13
    cc
    wcel
    @1
    @0
    @5
    cA
    recl
    recnd
    @1
    @12
    cB
    recl
    recnd
    @5
    @12
    mulcl
    syl2an
    @0
    @19
    @20
    @15
    cc
    wcel
    @1
    @21
    @22
    @8
    @14
    mulcl
    syl2an
    subnegd
    3eqtrd
end
