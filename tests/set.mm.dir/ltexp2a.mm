include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "crp.mm"
include "simpl1.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "simprl.mm"
include "lttrd.mm"
include "elrpd.mm"
include "simpl2.mm"
include "rpexpcl.mm"
include "syl2anc.mm"
include "rpred.mm"
include "recnd.mm"
include "mulid2d.mm"
include "cdiv.mm"
include "cmin.mm"
include "cn.mm"
include "simprr.mm"
include "wb.mm"
include "simpl3.mm"
include "znnsub.mm"
include "mpbid.mm"
include "expgt1.mm"
include "syl3anc.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "gt0ne0d.mm"
include "expsub.mm"
include "syl22anc.mm"
include "breqtrd.mm"
include "ltmuldivd.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"

theorem ltexp2a
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( ( A e. RR /\ M e. ZZ /\ N e. ZZ ) /\ ( 1 < A /\ M < N ) ) -> ( A ^ M ) < ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    c1
    cA
    clt
    wbr
    #
    cM
    cN
    clt
    wbr
    #
    wa
    #
    wa
    #
    c1
    cA
    cM
    cexp
    co
    #
    cmul
    co
    #
    @8
    cA
    cN
    cexp
    co
    #
    clt
    @7
    @8
    @7
    @8
    @7
    @8
    @7
    cA
    crp
    wcel
    #
    @1
    @8
    crp
    wcel
    @7
    cA
    @0
    @1
    @2
    @6
    simpl1
    #
    @7
    cc0
    c1
    cA
    @7
    0red
    @7
    1red
    #
    @12
    cc0
    c1
    clt
    wbr
    @7
    0lt1
    a1i
    @3
    @4
    @5
    simprl
    #
    lttrd
    #
    elrpd
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    cA
    cM
    rpexpcl
    syl2anc
    #
    rpred
    recnd
    mulid2d
    @7
    @9
    @10
    clt
    wbr
    c1
    @10
    @8
    cdiv
    co
    #
    clt
    wbr
    @7
    c1
    cA
    cN
    cM
    cmin
    co
    #
    cexp
    co
    #
    @19
    clt
    @7
    @0
    @20
    cn
    wcel
    #
    @4
    c1
    @21
    clt
    wbr
    @12
    @7
    @5
    @22
    @3
    @4
    @5
    simprr
    @7
    @1
    @2
    @5
    @22
    wb
    @17
    @0
    @1
    @2
    @6
    simpl3
    #
    cM
    cN
    znnsub
    syl2anc
    mpbid
    @14
    cA
    @20
    expgt1
    syl3anc
    @7
    cA
    cc
    wcel
    cA
    cc0
    wne
    @2
    @1
    @21
    @19
    wceq
    @7
    cA
    @12
    recnd
    @7
    cA
    @15
    gt0ne0d
    @23
    @17
    cA
    cN
    cM
    expsub
    syl22anc
    breqtrd
    @7
    c1
    @10
    @8
    @13
    @7
    @10
    @7
    @11
    @2
    @10
    crp
    wcel
    @16
    @23
    cA
    cN
    rpexpcl
    syl2anc
    rpred
    @18
    ltmuldivd
    mpbird
    eqbrtrrd
end
