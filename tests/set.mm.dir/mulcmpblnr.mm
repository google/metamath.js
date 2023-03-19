include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cpp.mm"
include "co.mm"
include "wceq.mm"
include "cmp.mm"
include "cop.mm"
include "cer.mm"
include "wbr.mm"
include "mulcmpblnrlem.mm"
include "wi.mm"
include "mulclpr.mm"
include "ad2ant2lr.mm"
include "simplll.mm"
include "simprll.mm"
include "syl2anc.mm"
include "simpllr.mm"
include "simprlr.mm"
include "addclpr.mm"
include "simplrl.mm"
include "simprrr.mm"
include "simplrr.mm"
include "simprrl.mm"
include "addcanpr.mm"
include "syl5.mm"
include "wb.mm"
include "syl2an.mm"
include "syl22anc.mm"
include "enrbreq.mm"
include "sylibrd.mm"

theorem mulcmpblnr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( ( A e. P. /\ B e. P. ) /\ ( C e. P. /\ D e. P. ) ) /\ ( ( F e. P. /\ G e. P. ) /\ ( R e. P. /\ S e. P. ) ) ) -> ( ( ( A +P. D ) = ( B +P. C ) /\ ( F +P. S ) = ( G +P. R ) ) -> <. ( ( A .P. F ) +P. ( B .P. G ) ) , ( ( A .P. G ) +P. ( B .P. F ) ) >. ~R <. ( ( C .P. R ) +P. ( D .P. S ) ) , ( ( C .P. S ) +P. ( D .P. R ) ) >. ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cC
    cnp
    wcel
    #
    cD
    cnp
    wcel
    #
    wa
    #
    wa
    #
    cF
    cnp
    wcel
    #
    cG
    cnp
    wcel
    #
    wa
    #
    cR
    cnp
    wcel
    #
    cS
    cnp
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    cA
    cD
    cpp
    co
    cB
    cC
    cpp
    co
    wceq
    cF
    cS
    cpp
    co
    cG
    cR
    cpp
    co
    wceq
    wa
    #
    cA
    cF
    cmp
    co
    #
    cB
    cG
    cmp
    co
    #
    cpp
    co
    #
    cC
    cS
    cmp
    co
    #
    cD
    cR
    cmp
    co
    #
    cpp
    co
    #
    cpp
    co
    #
    cA
    cG
    cmp
    co
    #
    cB
    cF
    cmp
    co
    #
    cpp
    co
    #
    cC
    cR
    cmp
    co
    #
    cD
    cS
    cmp
    co
    #
    cpp
    co
    #
    cpp
    co
    #
    wceq
    #
    @18
    @25
    cop
    @28
    @21
    cop
    cer
    wbr
    #
    @15
    cD
    cF
    cmp
    co
    #
    @22
    cpp
    co
    @32
    @29
    cpp
    co
    wceq
    #
    @14
    @30
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cG
    mulcmpblnrlem
    @14
    @32
    cnp
    wcel
    #
    @22
    cnp
    wcel
    #
    @33
    @30
    wi
    @5
    @9
    @34
    @2
    @12
    @4
    @7
    @34
    @3
    @8
    cD
    cF
    mulclpr
    ad2ant2lr
    ad2ant2lr
    @14
    @18
    cnp
    wcel
    #
    @21
    cnp
    wcel
    #
    @35
    @14
    @16
    cnp
    wcel
    #
    @17
    cnp
    wcel
    #
    @36
    @14
    @0
    @7
    @38
    @0
    @1
    @5
    @13
    simplll
    #
    @6
    @7
    @8
    @12
    simprll
    #
    cA
    cF
    mulclpr
    syl2anc
    @14
    @1
    @8
    @39
    @0
    @1
    @5
    @13
    simpllr
    #
    @6
    @7
    @8
    @12
    simprlr
    #
    cB
    cG
    mulclpr
    syl2anc
    @16
    @17
    addclpr
    syl2anc
    #
    @14
    @19
    cnp
    wcel
    #
    @20
    cnp
    wcel
    #
    @37
    @14
    @3
    @11
    @45
    @2
    @3
    @4
    @13
    simplrl
    #
    @6
    @9
    @10
    @11
    simprrr
    #
    cC
    cS
    mulclpr
    syl2anc
    @14
    @4
    @10
    @46
    @2
    @3
    @4
    @13
    simplrr
    #
    @6
    @9
    @10
    @11
    simprrl
    #
    cD
    cR
    mulclpr
    syl2anc
    @19
    @20
    addclpr
    syl2anc
    #
    @18
    @21
    addclpr
    syl2anc
    @32
    @22
    @29
    addcanpr
    syl2anc
    syl5
    @14
    @36
    @25
    cnp
    wcel
    #
    @28
    cnp
    wcel
    #
    @37
    @31
    @30
    wb
    @44
    @14
    @0
    @8
    @1
    @7
    @52
    @40
    @43
    @42
    @41
    @0
    @8
    wa
    @23
    cnp
    wcel
    @24
    cnp
    wcel
    @52
    @1
    @7
    wa
    cA
    cG
    mulclpr
    cB
    cF
    mulclpr
    @23
    @24
    addclpr
    syl2an
    syl22anc
    @14
    @3
    @10
    @4
    @11
    @53
    @47
    @50
    @49
    @48
    @3
    @10
    wa
    @26
    cnp
    wcel
    @27
    cnp
    wcel
    @53
    @4
    @11
    wa
    cC
    cR
    mulclpr
    cD
    cS
    mulclpr
    @26
    @27
    addclpr
    syl2an
    syl22anc
    @51
    @18
    @25
    @28
    @21
    enrbreq
    syl22anc
    sylibrd
end
