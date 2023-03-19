include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "crp.mm"
include "cz.mm"
include "simp1.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "0lt1.mm"
include "a1i.mm"
include "simp2.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "eluzel2.mm"
include "3ad2ant3.mm"
include "rpexpcl.mm"
include "syl2anc.mm"
include "rpred.mm"
include "recnd.mm"
include "mulid2d.mm"
include "cdiv.mm"
include "cmin.mm"
include "cn0.mm"
include "uznn0sub.mm"
include "expge1.mm"
include "syl3anc.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "gt0ne0d.mm"
include "eluzelz.mm"
include "expsub.mm"
include "syl22anc.mm"
include "breqtrd.mm"
include "lemuldivd.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"

theorem leexp2a
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. RR /\ 1 <_ A /\ N e. ( ZZ>= ` M ) ) -> ( A ^ M ) <_ ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    cN
    cM
    cuz
    cfv
    wcel
    #
    w3a
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
    @4
    cA
    cN
    cexp
    co
    #
    cle
    @3
    @4
    @3
    @4
    @3
    @4
    @3
    cA
    crp
    wcel
    #
    cM
    cz
    wcel
    #
    @4
    crp
    wcel
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    @3
    cc0
    c1
    cA
    @3
    0red
    @3
    1red
    #
    @9
    cc0
    c1
    clt
    wbr
    @3
    0lt1
    a1i
    @0
    @1
    @2
    simp2
    #
    ltletrd
    #
    elrpd
    #
    @2
    @0
    @8
    @1
    cM
    cN
    eluzel2
    3ad2ant3
    #
    cA
    cM
    rpexpcl
    syl2anc
    #
    rpred
    recnd
    mulid2d
    @3
    @5
    @6
    cle
    wbr
    c1
    @6
    @4
    cdiv
    co
    #
    cle
    wbr
    @3
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
    @16
    cle
    @3
    @0
    @17
    cn0
    wcel
    #
    @1
    c1
    @18
    cle
    wbr
    @9
    @2
    @0
    @19
    @1
    cM
    cN
    uznn0sub
    3ad2ant3
    @11
    cA
    @17
    expge1
    syl3anc
    @3
    cA
    cc
    wcel
    cA
    cc0
    wne
    cN
    cz
    wcel
    #
    @8
    @18
    @16
    wceq
    @3
    cA
    @9
    recnd
    @3
    cA
    @12
    gt0ne0d
    @2
    @0
    @20
    @1
    cM
    cN
    eluzelz
    3ad2ant3
    #
    @14
    cA
    cN
    cM
    expsub
    syl22anc
    breqtrd
    @3
    c1
    @6
    @4
    @10
    @3
    @6
    @3
    @7
    @20
    @6
    crp
    wcel
    @13
    @21
    cA
    cN
    rpexpcl
    syl2anc
    rpred
    @15
    lemuldivd
    mpbird
    eqbrtrrd
end
