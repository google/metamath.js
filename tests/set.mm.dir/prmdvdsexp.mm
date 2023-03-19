include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "bibi1d.mm"
include "imbi2d.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "exp1d.mm"
include "wo.mm"
include "cmul.mm"
include "cn0.mm"
include "nnnn0.mm"
include "expp1.mm"
include "syl2an.mm"
include "simpll.mm"
include "simpr.mm"
include "zexpcl.mm"
include "simplr.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "orbi1.mm"
include "oridm.mm"
include "syl6bb.mm"
include "bibi2d.mm"
include "syl5ibcom.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "3impa.mm"

theorem prmdvdsexp
  let cA: class A
  let cP: class P
  let cN: class N
  let vm: setvar m
  let vk: setvar k


  assert |- ( ( P e. Prime /\ A e. ZZ /\ N e. NN ) -> ( P || ( A ^ N ) <-> P || A ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    cP
    cA
    cN
    cexp
    co
    #
    cdvds
    wbr
    #
    cP
    cA
    cdvds
    wbr
    #
    wb
    #
    @2
    @0
    @1
    wa
    #
    @6
    @7
    cP
    cA
    vm
    cv
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    @5
    wb
    #
    wi
    @7
    cP
    cA
    c1
    cexp
    co
    #
    cdvds
    wbr
    #
    @5
    wb
    #
    wi
    @7
    cP
    cA
    vk
    cv
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    @5
    wb
    #
    wi
    @7
    cP
    cA
    @15
    c1
    caddc
    co
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    @5
    wb
    #
    wi
    @7
    @6
    wi
    vm
    vk
    cN
    @8
    c1
    wceq
    #
    @11
    @14
    @7
    @23
    @10
    @13
    @5
    @23
    @9
    @12
    cP
    cdvds
    @8
    c1
    cA
    cexp
    oveq2
    breq2d
    bibi1d
    imbi2d
    @8
    @15
    wceq
    #
    @11
    @18
    @7
    @24
    @10
    @17
    @5
    @24
    @9
    @16
    cP
    cdvds
    @8
    @15
    cA
    cexp
    oveq2
    breq2d
    bibi1d
    imbi2d
    @8
    @19
    wceq
    #
    @11
    @22
    @7
    @25
    @10
    @21
    @5
    @25
    @9
    @20
    cP
    cdvds
    @8
    @19
    cA
    cexp
    oveq2
    breq2d
    bibi1d
    imbi2d
    @8
    cN
    wceq
    #
    @11
    @6
    @7
    @26
    @10
    @4
    @5
    @26
    @9
    @3
    cP
    cdvds
    @8
    cN
    cA
    cexp
    oveq2
    breq2d
    bibi1d
    imbi2d
    @7
    @12
    cA
    cP
    cdvds
    @7
    cA
    @1
    cA
    cc
    wcel
    #
    @0
    cA
    zcn
    adantl
    #
    exp1d
    breq2d
    @15
    cn
    wcel
    #
    @7
    @18
    @22
    @7
    @29
    @18
    @22
    wi
    @7
    @29
    wa
    #
    @21
    @17
    @5
    wo
    #
    wb
    @18
    @22
    @30
    @21
    cP
    @16
    cA
    cmul
    co
    #
    cdvds
    wbr
    #
    @31
    @30
    @20
    @32
    cP
    cdvds
    @7
    @27
    @15
    cn0
    wcel
    #
    @20
    @32
    wceq
    @29
    @28
    @15
    nnnn0
    #
    cA
    @15
    expp1
    syl2an
    breq2d
    @30
    @0
    @16
    cz
    wcel
    #
    @1
    @33
    @31
    wb
    @0
    @1
    @29
    simpll
    @7
    @1
    @34
    @36
    @29
    @0
    @1
    simpr
    @35
    cA
    @15
    zexpcl
    syl2an
    @0
    @1
    @29
    simplr
    cP
    @16
    cA
    euclemma
    syl3anc
    bitrd
    @18
    @31
    @5
    @21
    @18
    @31
    @5
    @5
    wo
    @5
    @17
    @5
    @5
    orbi1
    @5
    oridm
    syl6bb
    bibi2d
    syl5ibcom
    expcom
    a2d
    nnind
    impcom
    3impa
end
