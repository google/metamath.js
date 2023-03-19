include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "simpr.mm"
include "crp.mm"
include "wb.mm"
include "0re.mm"
include "a1i.mm"
include "1re.mm"
include "cle.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "adantl.mm"
include "difrp.mm"
include "biimp3a.mm"
include "adantr.mm"
include "eqid.mm"
include "iccdil.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "simpl2.mm"
include "simpl1.mm"
include "resubcld.mm"
include "recnd.mm"
include "mul02d.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "eleqtrd.mm"
include "remulcld.mm"
include "iccshftr.mm"
include "mulcld.mm"
include "subadd23d.mm"
include "subdid.mm"
include "oveq1d.mm"
include "resubcl.mm"
include "sylancr.mm"
include "addcomd.mm"
include "1cnd.mm"
include "subdird.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "addid2d.mm"
include "npcand.mm"
include "3eltr3d.mm"

theorem lincmb01cmp
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( ( A e. RR /\ B e. RR /\ A < B ) /\ T e. ( 0 [,] 1 ) ) -> ( ( ( 1 - T ) x. A ) + ( T x. B ) ) e. ( A [,] B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cT
    cc0
    c1
    cicc
    co
    wcel
    #
    wa
    #
    cT
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    cA
    caddc
    co
    #
    cc0
    cA
    caddc
    co
    #
    @6
    cA
    caddc
    co
    #
    cicc
    co
    #
    c1
    cT
    cmin
    co
    #
    cA
    cmul
    co
    #
    cT
    cB
    cmul
    co
    #
    caddc
    co
    #
    cA
    cB
    cicc
    co
    @5
    @7
    cc0
    @6
    cicc
    co
    #
    wcel
    #
    @8
    @11
    wcel
    #
    @5
    @7
    cc0
    @6
    cmul
    co
    #
    c1
    @6
    cmul
    co
    #
    cicc
    co
    #
    @16
    @5
    @4
    @7
    @21
    wcel
    #
    @3
    @4
    simpr
    @5
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    cT
    cr
    wcel
    #
    @6
    crp
    wcel
    #
    @4
    @22
    wb
    @23
    @5
    0re
    a1i
    #
    @24
    @5
    1re
    a1i
    @4
    @25
    @3
    @4
    @25
    cc0
    cT
    cle
    wbr
    cT
    c1
    cle
    wbr
    cc0
    c1
    cT
    0re
    1re
    elicc2i
    simp1bi
    adantl
    #
    @3
    @26
    @4
    @0
    @1
    @2
    @26
    cA
    cB
    difrp
    biimp3a
    adantr
    cc0
    c1
    @19
    @20
    @6
    cT
    @19
    eqid
    @20
    eqid
    iccdil
    syl22anc
    mpbid
    @5
    @19
    cc0
    @20
    @6
    cicc
    @5
    @6
    @5
    @6
    @5
    cB
    cA
    @0
    @1
    @2
    @4
    simpl2
    #
    @0
    @1
    @2
    @4
    simpl1
    #
    resubcld
    #
    recnd
    #
    mul02d
    @5
    @6
    @32
    mulid2d
    oveq12d
    eleqtrd
    @5
    @23
    @6
    cr
    wcel
    @7
    cr
    wcel
    @0
    @17
    @18
    wb
    @27
    @31
    @5
    cT
    @6
    @28
    @31
    remulcld
    @30
    cc0
    @6
    @9
    @10
    cA
    @7
    @9
    eqid
    @10
    eqid
    iccshftr
    syl22anc
    mpbid
    @5
    @14
    cT
    cA
    cmul
    co
    #
    cmin
    co
    #
    cA
    caddc
    co
    @14
    cA
    @33
    cmin
    co
    #
    caddc
    co
    #
    @8
    @15
    @5
    @14
    @33
    cA
    @5
    cT
    cB
    @5
    cT
    @28
    recnd
    #
    @5
    cB
    @29
    recnd
    #
    mulcld
    #
    @5
    cT
    cA
    @37
    @5
    cA
    @30
    recnd
    #
    mulcld
    @40
    subadd23d
    @5
    @7
    @34
    cA
    caddc
    @5
    cT
    cB
    cA
    @37
    @38
    @40
    subdid
    oveq1d
    @5
    @15
    @14
    @13
    caddc
    co
    @36
    @5
    @13
    @14
    @5
    @13
    @5
    @12
    cA
    @5
    @24
    @25
    @12
    cr
    wcel
    1re
    @28
    c1
    cT
    resubcl
    sylancr
    @30
    remulcld
    recnd
    @39
    addcomd
    @5
    @13
    @35
    @14
    caddc
    @5
    @13
    c1
    cA
    cmul
    co
    #
    @33
    cmin
    co
    @35
    @5
    c1
    cT
    cA
    @5
    1cnd
    @37
    @40
    subdird
    @5
    @41
    cA
    @33
    cmin
    @5
    cA
    @40
    mulid2d
    oveq1d
    eqtrd
    oveq2d
    eqtrd
    3eqtr4d
    @5
    @9
    cA
    @10
    cB
    cicc
    @5
    cA
    @40
    addid2d
    @5
    cB
    cA
    @38
    @40
    npcand
    oveq12d
    3eltr3d
end
