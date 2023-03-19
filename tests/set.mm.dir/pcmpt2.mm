include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cpc.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "wn.mm"
include "wa.mm"
include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wne.mm"
include "cn.mm"
include "wceq.mm"
include "wf.mm"
include "pcmptcl.mm"
include "simprd.mm"
include "cuz.mm"
include "eluznn.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "pcmpt.mm"
include "oveq12d.mm"
include "cn0.mm"
include "wral.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "nn0cnd.mm"
include "subidd.mm"
include "adantr.mm"
include "cr.mm"
include "prmnn.mm"
include "syl.mm"
include "nnred.mm"
include "simpr.mm"
include "eluzle.mm"
include "letrd.mm"
include "iftrued.mm"
include "iftrue.mm"
include "adantl.mm"
include "nsyl3.mm"
include "iffalsed.mm"
include "3eqtr4d.mm"
include "iffalse.mm"
include "oveq2d.mm"
include "cc.mm"
include "0cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "subid1d.mm"
include "sylan9eqr.mm"
include "biantrud.mm"
include "ifbid.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"
include "3eqtrd.mm"

theorem pcmpt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  assume pcmpt.1: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ A ) , 1 ) )
  assume pcmpt.2: |- ( ph -> A. n e. Prime A e. NN0 )
  assume pcmpt.3: |- ( ph -> N e. NN )
  assume pcmpt.4: |- ( ph -> P e. Prime )
  assume pcmpt.5: |- ( n = P -> A = B )
  assume pcmpt2.6: |- ( ph -> M e. ( ZZ>= ` N ) )

  disjoint B n
  disjoint P n
  disjoint k m
  disjoint k p
  disjoint A k
  disjoint m p
  disjoint A m
  disjoint A p
  disjoint k n
  disjoint B k
  disjoint n p
  disjoint B p
  disjoint F k
  disjoint F p
  disjoint M p
  disjoint N p
  disjoint P k
  disjoint m n
  disjoint P m
  disjoint P p
  disjoint k ph
  disjoint p ph
  assert |- ( ph -> ( P pCnt ( ( seq 1 ( x. , F ) ` M ) / ( seq 1 ( x. , F ) ` N ) ) ) = if ( ( P <_ M /\ -. P <_ N ) , B , 0 ) )

  proof
    wph
    cP
    cM
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cN
    @0
    cfv
    #
    cdiv
    co
    cpc
    co
    #
    cP
    @1
    cpc
    co
    #
    cP
    @2
    cpc
    co
    #
    cmin
    co
    #
    cP
    cM
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    cP
    cN
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    cmin
    co
    #
    @7
    @9
    wn
    #
    wa
    #
    cB
    cc0
    cif
    #
    wph
    cP
    cprime
    wcel
    #
    @1
    cz
    wcel
    @1
    cc0
    wne
    @2
    cn
    wcel
    @3
    @6
    wceq
    pcmpt.4
    wph
    @1
    wph
    cn
    cn
    cM
    @0
    wph
    cn
    cn
    cF
    wf
    cn
    cn
    @0
    wf
    wph
    cA
    vn
    cF
    pcmpt.1
    pcmpt.2
    pcmptcl
    simprd
    #
    wph
    cN
    cn
    wcel
    cM
    cN
    cuz
    cfv
    wcel
    #
    cM
    cn
    wcel
    pcmpt.3
    pcmpt2.6
    cM
    cN
    eluznn
    syl2anc
    #
    ffvelrnd
    #
    nnzd
    wph
    @1
    @19
    nnne0d
    wph
    cn
    cn
    cN
    @0
    @16
    pcmpt.3
    ffvelrnd
    @1
    @2
    cP
    pcdiv
    syl121anc
    wph
    @4
    @8
    @5
    @10
    cmin
    wph
    cA
    cB
    cP
    vn
    cF
    cM
    pcmpt.1
    pcmpt.2
    @18
    pcmpt.4
    pcmpt.5
    pcmpt
    wph
    cA
    cB
    cP
    vn
    cF
    cN
    pcmpt.1
    pcmpt.2
    pcmpt.3
    pcmpt.4
    pcmpt.5
    pcmpt
    oveq12d
    wph
    @9
    @11
    @14
    wceq
    wph
    @9
    wa
    #
    cB
    cB
    cmin
    co
    #
    cc0
    @11
    @14
    wph
    @21
    cc0
    wceq
    @9
    wph
    cB
    wph
    cB
    wph
    @15
    cA
    cn0
    wcel
    #
    vn
    cprime
    wral
    cB
    cn0
    wcel
    #
    pcmpt.4
    pcmpt.2
    @22
    @23
    vn
    cP
    cprime
    vn
    cv
    cP
    wceq
    cA
    cB
    cn0
    pcmpt.5
    eleq1d
    rspcv
    sylc
    nn0cnd
    #
    subidd
    adantr
    @20
    @8
    cB
    @10
    cB
    cmin
    @20
    @7
    cB
    cc0
    @20
    cP
    cN
    cM
    wph
    cP
    cr
    wcel
    @9
    wph
    cP
    wph
    @15
    cP
    cn
    wcel
    pcmpt.4
    cP
    prmnn
    syl
    nnred
    adantr
    wph
    cN
    cr
    wcel
    @9
    wph
    cN
    pcmpt.3
    nnred
    adantr
    wph
    cM
    cr
    wcel
    @9
    wph
    cM
    @18
    nnred
    adantr
    wph
    @9
    simpr
    #
    wph
    cN
    cM
    cle
    wbr
    #
    @9
    wph
    @17
    @26
    pcmpt2.6
    cN
    cM
    eluzle
    syl
    adantr
    letrd
    iftrued
    @9
    @10
    cB
    wceq
    wph
    @9
    cB
    cc0
    iftrue
    adantl
    oveq12d
    @20
    @13
    cB
    cc0
    @13
    @9
    @20
    @7
    @12
    simpr
    @25
    nsyl3
    iffalsed
    3eqtr4d
    wph
    @12
    wa
    #
    @11
    @8
    @14
    @12
    wph
    @11
    @8
    cc0
    cmin
    co
    @8
    @12
    @10
    cc0
    @8
    cmin
    @9
    cB
    cc0
    iffalse
    oveq2d
    wph
    @8
    wph
    cB
    cc
    wcel
    cc0
    cc
    wcel
    @8
    cc
    wcel
    @24
    0cn
    @7
    cB
    cc0
    cc
    ifcl
    sylancl
    subid1d
    sylan9eqr
    @27
    @7
    @13
    cB
    cc0
    @27
    @12
    @7
    wph
    @12
    simpr
    biantrud
    ifbid
    eqtrd
    pm2.61dan
    3eqtrd
end
