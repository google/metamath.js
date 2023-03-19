include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "simplll.mm"
include "simpllr.mm"
include "subcld.mm"
include "abscl.mm"
include "syl.mm"
include "simplrl.mm"
include "readdcld.mm"
include "simplrr.mm"
include "cle.mm"
include "abs3dif.mm"
include "syl3anc.mm"
include "simprl.mm"
include "simprr.mm"
include "lt2halvesd.mm"
include "lelttrd.mm"
include "ex.mm"

theorem abs3lem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. RR ) ) -> ( ( ( abs ` ( A - C ) ) < ( D / 2 ) /\ ( abs ` ( C - B ) ) < ( D / 2 ) ) -> ( abs ` ( A - B ) ) < D ) )

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
    cC
    cc
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cA
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cD
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cC
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    wa
    #
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    cD
    clt
    wbr
    @6
    @14
    wa
    #
    @16
    @8
    @12
    caddc
    co
    #
    cD
    @17
    @15
    cc
    wcel
    @16
    cr
    wcel
    @17
    cA
    cB
    @0
    @1
    @5
    @14
    simplll
    #
    @0
    @1
    @5
    @14
    simpllr
    #
    subcld
    @15
    abscl
    syl
    @17
    @8
    @12
    @17
    @7
    cc
    wcel
    @8
    cr
    wcel
    @17
    cA
    cC
    @19
    @2
    @3
    @4
    @14
    simplrl
    #
    subcld
    @7
    abscl
    syl
    #
    @17
    @11
    cc
    wcel
    @12
    cr
    wcel
    @17
    cC
    cB
    @21
    @20
    subcld
    @11
    abscl
    syl
    #
    readdcld
    @2
    @3
    @4
    @14
    simplrr
    #
    @17
    @0
    @1
    @3
    @16
    @18
    cle
    wbr
    @19
    @20
    @21
    cA
    cB
    cC
    abs3dif
    syl3anc
    @17
    @8
    @12
    cD
    @22
    @23
    @24
    @6
    @10
    @13
    simprl
    @6
    @10
    @13
    simprr
    lt2halvesd
    lelttrd
    ex
end
