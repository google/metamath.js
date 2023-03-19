include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cdgr.mm"
include "wceq.mm"
include "cn.mm"
include "ccoe.mm"
include "w3a.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "c0p.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "simpr2.mm"
include "cc0.mm"
include "dgr0.mm"
include "nngt0.mm"
include "syl5eqbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "syl.mm"
include "wo.mm"
include "cle.mm"
include "cif.mm"
include "cc.mm"
include "plyssc.mm"
include "sseli.mm"
include "eqid.mm"
include "dgrsub.mm"
include "syl2an.mm"
include "adantr.mm"
include "simpr1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ifeq12d.mm"
include "ifid.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "coesub.mm"
include "fveq1d.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "coef3.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "ad2antlr.mm"
include "nn0ex.mm"
include "inidm.mm"
include "simplr3.mm"
include "eqidd.mm"
include "ofval.mm"
include "mpdan.mm"
include "ffvelrnd.mm"
include "subidd.mm"
include "3eqtrd.mm"
include "wb.mm"
include "plysubcl.mm"
include "dgrlt.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ord.mm"
include "pm2.61d.mm"

theorem dgrsub2
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  assume dgrsub2.a: |- N = ( deg ` F )


  assert |- ( ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` T ) ) /\ ( ( deg ` G ) = N /\ N e. NN /\ ( ( coeff ` F ) ` N ) = ( ( coeff ` G ) ` N ) ) ) -> ( deg ` ( F oF - G ) ) < N )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    cT
    cply
    cfv
    #
    wcel
    #
    wa
    #
    cG
    cdgr
    cfv
    #
    cN
    wceq
    #
    cN
    cn
    wcel
    #
    cN
    cF
    ccoe
    cfv
    #
    cfv
    cN
    cG
    ccoe
    cfv
    #
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    cF
    cG
    cmin
    cof
    #
    co
    #
    c0p
    wceq
    #
    @15
    cdgr
    cfv
    #
    cN
    clt
    wbr
    #
    @13
    @7
    @16
    @18
    wi
    @4
    @6
    @7
    @11
    simpr2
    #
    @7
    @18
    @16
    c0p
    cdgr
    cfv
    #
    cN
    clt
    wbr
    @7
    @20
    cc0
    cN
    clt
    dgr0
    cN
    nngt0
    syl5eqbr
    @16
    @17
    @20
    cN
    clt
    @15
    c0p
    cdgr
    fveq2
    breq1d
    syl5ibrcom
    syl
    @13
    @16
    @18
    @13
    @16
    @18
    wo
    #
    @17
    cN
    cle
    wbr
    #
    cN
    @15
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @13
    @17
    cF
    cdgr
    cfv
    #
    @5
    cle
    wbr
    #
    @5
    @26
    cif
    #
    cN
    cle
    @4
    @17
    @28
    cle
    wbr
    #
    @12
    @1
    cF
    cc
    cply
    cfv
    #
    wcel
    #
    cG
    @30
    wcel
    #
    @29
    @3
    @0
    @30
    cF
    cS
    plyssc
    sseli
    #
    @2
    @30
    cG
    cT
    plyssc
    sseli
    #
    cc
    cF
    cG
    @26
    @5
    @26
    eqid
    @5
    eqid
    dgrsub
    syl2an
    adantr
    @13
    @28
    @27
    cN
    cN
    cif
    cN
    @13
    @27
    @5
    cN
    @26
    cN
    @4
    @6
    @7
    @11
    simpr1
    @26
    cN
    wceq
    @13
    cN
    @26
    dgrsub2.a
    eqcomi
    a1i
    ifeq12d
    @27
    cN
    ifid
    syl6eq
    breqtrd
    @13
    @24
    cN
    @8
    @9
    @14
    co
    #
    cfv
    #
    @10
    @10
    cmin
    co
    #
    cc0
    @13
    cN
    @23
    @35
    @4
    @23
    @35
    wceq
    #
    @12
    @1
    @31
    @32
    @38
    @3
    @33
    @34
    @8
    @9
    cc
    cF
    cG
    @8
    eqid
    #
    @9
    eqid
    #
    coesub
    syl2an
    adantr
    fveq1d
    @13
    cN
    cn0
    wcel
    #
    @36
    @37
    wceq
    @13
    cN
    @19
    nnnn0d
    #
    @13
    cn0
    cn0
    @10
    @10
    cmin
    cn0
    @8
    @9
    cvv
    cvv
    cN
    @13
    cn0
    cc
    @8
    wf
    #
    @8
    cn0
    wfn
    @1
    @43
    @3
    @12
    @8
    cS
    cF
    @39
    coef3
    ad2antrr
    cn0
    cc
    @8
    ffn
    syl
    @13
    cn0
    cc
    @9
    wf
    #
    @9
    cn0
    wfn
    @3
    @44
    @1
    @12
    @9
    cT
    cG
    @40
    coef3
    ad2antlr
    #
    cn0
    cc
    @9
    ffn
    syl
    cn0
    cvv
    wcel
    @13
    nn0ex
    a1i
    #
    @46
    cn0
    inidm
    @6
    @7
    @11
    @4
    @41
    simplr3
    @13
    @41
    wa
    @10
    eqidd
    ofval
    mpdan
    @13
    @10
    @13
    cn0
    cc
    cN
    @9
    @45
    @42
    ffvelrnd
    subidd
    3eqtrd
    @13
    @15
    @30
    wcel
    #
    @41
    @21
    @22
    @25
    wa
    wb
    @4
    @47
    @12
    @1
    @31
    @32
    @47
    @3
    @33
    @34
    cc
    cF
    cG
    plysubcl
    syl2an
    adantr
    @42
    @23
    cc
    @15
    cN
    @17
    @17
    eqid
    @23
    eqid
    dgrlt
    syl2anc
    mpbir2and
    ord
    pm2.61d
end
