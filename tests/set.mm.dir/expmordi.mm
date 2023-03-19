include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cc.mm"
include "wb.mm"
include "recn.mm"
include "exp1.mm"
include "breqan12d.mm"
include "syl2an.mm"
include "biimpar.mm"
include "adantrl.mm"
include "w3a.mm"
include "cmul.mm"
include "simp2ll.mm"
include "cn0.mm"
include "nnnn0.mm"
include "3ad2ant1.mm"
include "reexpcld.mm"
include "simp2lr.mm"
include "jca.mm"
include "simp2rl.mm"
include "expge0d.mm"
include "simp3.mm"
include "simp2l.mm"
include "simp2r.mm"
include "ltmul12a.mm"
include "syl22anc.mm"
include "recnd.mm"
include "expp1d.mm"
include "3brtr4d.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "3impa.mm"

theorem expmordi
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ A < B ) /\ N e. NN ) -> ( A ^ N ) < ( B ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    cN
    cn
    wcel
    #
    cA
    cN
    cexp
    co
    #
    cB
    cN
    cexp
    co
    #
    clt
    wbr
    #
    @6
    @2
    @5
    wa
    #
    @9
    @10
    cA
    va
    cv
    #
    cexp
    co
    #
    cB
    @11
    cexp
    co
    #
    clt
    wbr
    #
    wi
    @10
    cA
    c1
    cexp
    co
    #
    cB
    c1
    cexp
    co
    #
    clt
    wbr
    #
    wi
    @10
    cA
    vb
    cv
    #
    cexp
    co
    #
    cB
    @18
    cexp
    co
    #
    clt
    wbr
    #
    wi
    @10
    cA
    @18
    c1
    caddc
    co
    #
    cexp
    co
    #
    cB
    @22
    cexp
    co
    #
    clt
    wbr
    #
    wi
    @10
    @9
    wi
    va
    vb
    cN
    @11
    c1
    wceq
    #
    @14
    @17
    @10
    @26
    @12
    @15
    @13
    @16
    clt
    @11
    c1
    cA
    cexp
    oveq2
    @11
    c1
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    va
    vb
    weq
    #
    @14
    @21
    @10
    @27
    @12
    @19
    @13
    @20
    clt
    @11
    @18
    cA
    cexp
    oveq2
    @11
    @18
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @11
    @22
    wceq
    #
    @14
    @25
    @10
    @28
    @12
    @23
    @13
    @24
    clt
    @11
    @22
    cA
    cexp
    oveq2
    @11
    @22
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @11
    cN
    wceq
    #
    @14
    @9
    @10
    @29
    @12
    @7
    @13
    @8
    clt
    @11
    cN
    cA
    cexp
    oveq2
    @11
    cN
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @2
    @4
    @17
    @3
    @2
    @17
    @4
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @17
    @4
    wb
    @1
    cA
    recn
    cB
    recn
    @30
    @31
    @15
    cA
    @16
    cB
    clt
    cA
    exp1
    cB
    exp1
    breqan12d
    syl2an
    biimpar
    adantrl
    @18
    cn
    wcel
    #
    @10
    @21
    @25
    @32
    @10
    @21
    @25
    @32
    @10
    @21
    w3a
    #
    @19
    cA
    cmul
    co
    #
    @20
    cB
    cmul
    co
    #
    @23
    @24
    clt
    @33
    @19
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    wa
    cc0
    @19
    cle
    wbr
    #
    @21
    wa
    @2
    @5
    @34
    @35
    clt
    wbr
    @33
    @36
    @37
    @33
    cA
    @18
    @0
    @1
    @5
    @32
    @21
    simp2ll
    #
    @32
    @10
    @18
    cn0
    wcel
    @21
    @18
    nnnn0
    3ad2ant1
    #
    reexpcld
    @33
    cB
    @18
    @0
    @1
    @5
    @32
    @21
    simp2lr
    #
    @40
    reexpcld
    jca
    @33
    @38
    @21
    @33
    cA
    @18
    @39
    @40
    @3
    @4
    @2
    @32
    @21
    simp2rl
    expge0d
    @32
    @10
    @21
    simp3
    jca
    @32
    @2
    @5
    @21
    simp2l
    @32
    @2
    @5
    @21
    simp2r
    @19
    @20
    cA
    cB
    ltmul12a
    syl22anc
    @33
    cA
    @18
    @33
    cA
    @39
    recnd
    @40
    expp1d
    @33
    cB
    @18
    @33
    cB
    @41
    recnd
    @40
    expp1d
    3brtr4d
    3exp
    a2d
    nnind
    impcom
    3impa
end
