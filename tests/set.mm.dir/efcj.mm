include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "cn0.mm"
include "ccj.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "ce.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "cjcl.mm"
include "eqid.mm"
include "efcvg.mm"
include "syl.mm"
include "cvv.mm"
include "nn0uz.mm"
include "seqex.mm"
include "a1i.mm"
include "0zd.mm"
include "wa.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "eqeltrd.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "addcl.mm"
include "cfz.mm"
include "simpl.mm"
include "elfznn0.mm"
include "syl2an.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cjadd.mm"
include "expcl.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "cjdivd.mm"
include "cjexp.mm"
include "nnred.mm"
include "cjred.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "seqhomo.mm"
include "eqcomd.mm"
include "climcj.mm"
include "climuni.mm"
include "syl2anc.mm"

theorem efcj
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- ( A e. CC -> ( exp ` ( * ` A ) ) = ( * ` ( exp ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    caddc
    vn
    cn0
    cA
    ccj
    cfv
    #
    vn
    cv
    #
    cexp
    co
    @2
    cfa
    cfv
    #
    cdiv
    co
    cmpt
    #
    cc0
    cseq
    #
    @1
    ce
    cfv
    #
    cli
    wbr
    #
    @5
    cA
    ce
    cfv
    #
    ccj
    cfv
    #
    cli
    wbr
    @6
    @9
    wceq
    @0
    @1
    cc
    wcel
    @7
    cA
    cjcl
    @1
    vn
    @4
    @4
    eqid
    #
    efcvg
    syl
    @0
    @8
    vj
    caddc
    vn
    cn0
    cA
    @2
    cexp
    co
    @3
    cdiv
    co
    cmpt
    #
    cc0
    cseq
    #
    @5
    cc0
    cvv
    cn0
    nn0uz
    cA
    vn
    @11
    @11
    eqid
    #
    efcvg
    @5
    cvv
    wcel
    @0
    caddc
    @4
    cc0
    seqex
    a1i
    @0
    0zd
    #
    @0
    cn0
    cc
    vj
    cv
    #
    @12
    @0
    vk
    @11
    cc0
    cn0
    nn0uz
    @14
    @0
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @16
    @11
    cfv
    #
    cA
    @16
    cexp
    co
    #
    @16
    cfa
    cfv
    #
    cdiv
    co
    #
    cc
    @17
    @19
    @22
    wceq
    @0
    cA
    vn
    @11
    @16
    @13
    eftval
    adantl
    #
    cA
    @16
    eftcl
    eqeltrd
    #
    serf
    ffvelrnda
    @0
    @15
    cn0
    wcel
    #
    wa
    #
    @15
    @12
    cfv
    ccj
    cfv
    @15
    @5
    cfv
    @26
    vk
    vm
    caddc
    caddc
    cc
    @11
    @4
    ccj
    cc0
    @15
    @16
    cc
    wcel
    vm
    cv
    #
    cc
    wcel
    wa
    #
    @16
    @27
    caddc
    co
    #
    cc
    wcel
    @26
    @16
    @27
    addcl
    adantl
    @26
    @0
    @17
    @19
    cc
    wcel
    @16
    cc0
    @15
    cfz
    co
    wcel
    #
    @0
    @25
    simpl
    #
    @16
    @15
    elfznn0
    #
    @24
    syl2an
    @26
    @15
    cn0
    cc0
    cuz
    cfv
    @0
    @25
    simpr
    nn0uz
    syl6eleq
    @28
    @29
    ccj
    cfv
    @16
    ccj
    cfv
    @27
    ccj
    cfv
    caddc
    co
    wceq
    @26
    @16
    @27
    cjadd
    adantl
    @26
    @0
    @17
    @19
    ccj
    cfv
    #
    @16
    @4
    cfv
    #
    wceq
    @30
    @31
    @32
    @18
    @22
    ccj
    cfv
    #
    @1
    @16
    cexp
    co
    #
    @21
    cdiv
    co
    #
    @33
    @34
    @18
    @35
    @20
    ccj
    cfv
    #
    @21
    ccj
    cfv
    #
    cdiv
    co
    @37
    @18
    @20
    @21
    cA
    @16
    expcl
    @18
    @21
    @17
    @21
    cn
    wcel
    @0
    @16
    faccl
    adantl
    #
    nncnd
    @18
    @21
    @40
    nnne0d
    cjdivd
    @18
    @38
    @36
    @39
    @21
    cdiv
    cA
    @16
    cjexp
    @18
    @21
    @18
    @21
    @40
    nnred
    cjred
    oveq12d
    eqtrd
    @18
    @19
    @22
    ccj
    @23
    fveq2d
    @17
    @34
    @37
    wceq
    @0
    @1
    vn
    @4
    @16
    @10
    eftval
    adantl
    3eqtr4d
    syl2an
    seqhomo
    eqcomd
    climcj
    @6
    @9
    @5
    climuni
    syl2anc
end
