include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "wral.mm"
include "cc0.mm"
include "wa.mm"
include "cc.mm"
include "fveecn.mm"
include "subid.mm"
include "sq0id.mm"
include "syl.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "fzfid.mm"
include "cuz.mm"
include "wss.mm"
include "sumz.mm"
include "olcs.mm"
include "eqtrd.mm"
include "3ad2ant3.mm"
include "eqeq2d.mm"
include "wb.mm"
include "cr.mm"
include "fveere.mm"
include "adantlr.mm"
include "adantll.mm"
include "resubcld.mm"
include "resqcld.mm"
include "sqge0d.mm"
include "fsum00.mm"
include "subcl.mm"
include "sqeq0.mm"
include "subeq0.mm"
include "bitrd.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralbidva.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "brcgr.mm"
include "syl22anc.mm"
include "eqeefv.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "adantl.mm"

theorem axcgrid
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vi: setvar i


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , C >. -> A = B ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cA
    cB
    cop
    cC
    cC
    cop
    ccgr
    wbr
    #
    cA
    cB
    wceq
    #
    wi
    cN
    cn
    wcel
    @4
    @5
    @6
    @4
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cA
    cfv
    #
    @8
    cB
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @7
    @8
    cC
    cfv
    #
    @14
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    wceq
    #
    @9
    @10
    wceq
    #
    vi
    @7
    wral
    #
    @5
    @6
    @4
    @18
    @13
    cc0
    wceq
    #
    @20
    @4
    @17
    cc0
    @13
    @3
    @1
    @17
    cc0
    wceq
    @2
    @3
    @17
    @7
    cc0
    vi
    csu
    #
    cc0
    @3
    @7
    @16
    cc0
    vi
    @3
    @8
    @7
    wcel
    #
    wa
    @14
    cc
    wcel
    #
    @16
    cc0
    wceq
    cC
    @8
    cN
    fveecn
    @24
    @15
    @14
    subid
    sq0id
    syl
    sumeq2dv
    @3
    @7
    cfn
    wcel
    #
    @22
    cc0
    wceq
    #
    @3
    c1
    cN
    fzfid
    @7
    c1
    cuz
    cfv
    wss
    @25
    @26
    @7
    vi
    c1
    sumz
    olcs
    syl
    eqtrd
    3ad2ant3
    eqeq2d
    @1
    @2
    @21
    @20
    wb
    @3
    @1
    @2
    wa
    #
    @21
    @12
    cc0
    wceq
    #
    vi
    @7
    wral
    @20
    @27
    @7
    @12
    vi
    @27
    c1
    cN
    fzfid
    @27
    @23
    wa
    #
    @11
    @29
    @9
    @10
    @1
    @23
    @9
    cr
    wcel
    @2
    cA
    @8
    cN
    fveere
    adantlr
    @2
    @23
    @10
    cr
    wcel
    @1
    cB
    @8
    cN
    fveere
    adantll
    resubcld
    #
    resqcld
    @29
    @11
    @30
    sqge0d
    fsum00
    @27
    @28
    @19
    vi
    @7
    @1
    @2
    @23
    @28
    @19
    wb
    #
    @1
    @23
    wa
    @9
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    @31
    @2
    @23
    wa
    cA
    @8
    cN
    fveecn
    cB
    @8
    cN
    fveecn
    @32
    @33
    wa
    #
    @28
    @11
    cc0
    wceq
    #
    @19
    @34
    @11
    cc
    wcel
    @28
    @35
    wb
    @9
    @10
    subcl
    @11
    sqeq0
    syl
    @9
    @10
    subeq0
    bitrd
    syl2an
    anandirs
    ralbidva
    bitrd
    3adant3
    bitrd
    @4
    @1
    @2
    @3
    @3
    @5
    @18
    wb
    @1
    @2
    @3
    simp1
    @1
    @2
    @3
    simp2
    @1
    @2
    @3
    simp3
    #
    @36
    cA
    cB
    cC
    cC
    vi
    cN
    brcgr
    syl22anc
    @1
    @2
    @6
    @20
    wb
    @3
    cA
    cB
    vi
    cN
    eqeefv
    3adant3
    3bitr4d
    biimpd
    adantl
end
