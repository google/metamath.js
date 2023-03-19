include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wceq.mm"
include "wi.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "cgrid2.mm"
include "syl13anc.mm"
include "simp2l.mm"
include "axbtwnid.mm"
include "syl3anc.mm"
include "opeq1.mm"
include "breq12d.mm"
include "imbi1d.mm"
include "biimpcd.mm"
include "ax-1.mm"
include "syl8.mm"
include "sylsyld.mm"
include "3impd.mm"
include "opeq2.mm"
include "breq2d.mm"
include "3anbi1d.mm"
include "syl5ib.mm"
include "wne.mm"
include "ccolin.mm"
include "simpr1.mm"
include "simpr2l.mm"
include "simpr2r.mm"
include "simpr3l.mm"
include "btwncolinear1.mm"
include "idd.mm"
include "3anim123d.mm"
include "anim2i.mm"
include "3simpc.mm"
include "adantl.mm"
include "jca.mm"
include "lineid.mm"
include "syl5.mm"
include "expd.mm"
include "impcom.mm"
include "syld.mm"
include "ex.mm"
include "pm2.61ine.mm"

theorem idinside
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( C Btwn <. A , B >. /\ <. A , C >. Cgr <. A , D >. /\ <. B , C >. Cgr <. B , D >. ) -> C = D ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cC
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    cA
    cC
    cop
    #
    cA
    cD
    cop
    #
    ccgr
    wbr
    #
    cB
    cC
    cop
    #
    cB
    cD
    cop
    ccgr
    wbr
    #
    w3a
    #
    cC
    cD
    wceq
    #
    wi
    #
    wi
    cA
    cB
    @8
    cC
    cA
    cA
    cop
    #
    cbtwn
    wbr
    #
    @13
    @15
    w3a
    #
    @17
    wi
    cA
    cB
    wceq
    #
    @18
    @8
    @20
    @13
    @15
    @17
    @8
    cC
    cC
    cop
    #
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    @17
    wi
    #
    @20
    cC
    cA
    wceq
    #
    @13
    @15
    @17
    wi
    #
    wi
    @8
    @0
    @5
    @5
    @6
    @26
    @0
    @4
    @7
    simp1
    #
    @0
    @4
    @5
    @6
    simp3l
    #
    @30
    @0
    @4
    @5
    @6
    simp3r
    cC
    cC
    cD
    cN
    cgrid2
    syl13anc
    @8
    @0
    @5
    @2
    @20
    @27
    wi
    @29
    @30
    @0
    @2
    @3
    @7
    simp2l
    cC
    cA
    cN
    axbtwnid
    syl3anc
    @26
    @27
    @13
    @17
    @28
    @27
    @26
    @13
    @17
    wi
    @27
    @25
    @13
    @17
    @27
    @23
    @11
    @24
    @12
    ccgr
    cC
    cA
    cC
    opeq1
    cC
    cA
    cD
    opeq1
    breq12d
    imbi1d
    biimpcd
    @17
    @15
    ax-1
    syl8
    sylsyld
    3impd
    @22
    @21
    @16
    @17
    @22
    @20
    @10
    @13
    @15
    @22
    @19
    @9
    cC
    cbtwn
    cA
    cB
    cA
    opeq2
    breq2d
    3anbi1d
    imbi1d
    syl5ib
    cA
    cB
    wne
    #
    @8
    @18
    @31
    @8
    wa
    #
    @16
    cA
    @14
    ccolin
    wbr
    #
    @13
    @15
    w3a
    #
    @17
    @32
    @10
    @33
    @13
    @13
    @15
    @15
    @32
    @0
    @2
    @3
    @5
    @10
    @33
    wi
    @31
    @0
    @4
    @7
    simpr1
    @2
    @3
    @0
    @7
    @31
    simpr2l
    @2
    @3
    @0
    @7
    @31
    simpr2r
    @5
    @6
    @0
    @4
    @31
    simpr3l
    cA
    cB
    cC
    cN
    btwncolinear1
    syl13anc
    @32
    @13
    idd
    @32
    @15
    idd
    3anim123d
    @8
    @31
    @34
    @17
    wi
    @8
    @31
    @34
    @17
    @31
    @34
    wa
    #
    @31
    @33
    wa
    #
    @13
    @15
    wa
    #
    wa
    @8
    @17
    @35
    @36
    @37
    @34
    @33
    @31
    @33
    @13
    @15
    simp1
    anim2i
    @34
    @37
    @31
    @33
    @13
    @15
    3simpc
    adantl
    jca
    cA
    cB
    cC
    cD
    cN
    lineid
    syl5
    expd
    impcom
    syld
    ex
    pm2.61ine
end
