include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cmin.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cabs.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cim.mm"
include "cexp.mm"
include "caddc.mm"
include "csqrt.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wi.mm"
include "simplr.mm"
include "simpll.mm"
include "subcld.mm"
include "recld.mm"
include "recnd.mm"
include "abscld.mm"
include "absge0d.mm"
include "jca.mm"
include "imcld.mm"
include "simpr.mm"
include "sqsscirc1.mm"
include "syl21anc.mm"
include "absval2d.mm"
include "breq1d.mm"
include "wceq.mm"
include "absresq.mm"
include "syl.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "bitr4d.mm"
include "sylibrd.mm"

theorem sqsscirc2
  let cA: class A
  let cB: class B
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ D e. RR+ ) -> ( ( ( abs ` ( Re ` ( B - A ) ) ) < ( D / 2 ) /\ ( abs ` ( Im ` ( B - A ) ) ) < ( D / 2 ) ) -> ( abs ` ( B - A ) ) < D ) )

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
    cD
    crp
    wcel
    #
    wa
    #
    cB
    cA
    cmin
    co
    #
    cre
    cfv
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
    @5
    cim
    cfv
    #
    cabs
    cfv
    #
    @8
    clt
    wbr
    wa
    #
    @7
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    clt
    wbr
    #
    @5
    cabs
    cfv
    #
    cD
    clt
    wbr
    #
    @4
    @7
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    wa
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    @3
    @11
    @16
    wi
    @4
    @19
    @20
    @4
    @6
    @4
    @6
    @4
    @5
    @4
    cB
    cA
    @0
    @1
    @3
    simplr
    @0
    @1
    @3
    simpll
    subcld
    #
    recld
    #
    recnd
    #
    abscld
    @4
    @6
    @25
    absge0d
    jca
    @4
    @21
    @22
    @4
    @9
    @4
    @9
    @4
    @5
    @23
    imcld
    #
    recnd
    #
    abscld
    @4
    @9
    @27
    absge0d
    jca
    @2
    @3
    simpr
    cD
    @7
    @10
    sqsscirc1
    syl21anc
    @4
    @18
    @6
    c2
    cexp
    co
    #
    @9
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    clt
    wbr
    @16
    @4
    @17
    @31
    cD
    clt
    @4
    @5
    @23
    absval2d
    breq1d
    @4
    @15
    @31
    cD
    clt
    @4
    @14
    @30
    csqrt
    @4
    @12
    @28
    @13
    @29
    caddc
    @4
    @6
    cr
    wcel
    @12
    @28
    wceq
    @24
    @6
    absresq
    syl
    @4
    @9
    cr
    wcel
    @13
    @29
    wceq
    @26
    @9
    absresq
    syl
    oveq12d
    fveq2d
    breq1d
    bitr4d
    sylibrd
end
