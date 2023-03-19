include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "wral.mm"
include "ciun.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "wi.mm"
include "brdom2.mm"
include "com.mm"
include "nnenom.mm"
include "sdomentr.mm"
include "mpan2.mm"
include "cfn.mm"
include "isfinite.mm"
include "finiunmbl.mm"
include "ex.mm"
include "sylbir.mm"
include "syl.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "wa.mm"
include "ccnv.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "wrex.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcri.mm"
include "nfrex.mm"
include "w3a.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "3adant3.mm"
include "simp3.mm"
include "f1ocnvfv1.mm"
include "eqcomd.mm"
include "csbeq1a.mm"
include "eleqtrd.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "f1ocnvdm.mm"
include "rspce.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "adantr.mm"
include "rspcsbela.mm"
include "sylan.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "iunmbl.mm"
include "eqeltrd.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "jaoi.mm"
include "imp.mm"

theorem iunmbl2
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x

  disjoint A n
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A x
  disjoint B f
  disjoint B k
  disjoint B x
  assert |- ( ( A ~<_ NN /\ A. n e. A B e. dom vol ) -> U_ n e. A B e. dom vol )

  proof
    cA
    cn
    cdom
    wbr
    #
    cB
    cvol
    cdm
    #
    wcel
    vn
    cA
    wral
    #
    vn
    cA
    cB
    ciun
    #
    @1
    wcel
    #
    @0
    cA
    cn
    csdm
    wbr
    #
    cA
    cn
    cen
    wbr
    #
    wo
    @2
    @4
    wi
    #
    cA
    cn
    brdom2
    @5
    @7
    @6
    @5
    cA
    com
    csdm
    wbr
    #
    @7
    @5
    cn
    com
    cen
    wbr
    @8
    nnenom
    cA
    cn
    com
    sdomentr
    mpan2
    @8
    cA
    cfn
    wcel
    #
    @7
    cA
    isfinite
    @9
    @2
    @4
    cA
    cB
    vn
    finiunmbl
    ex
    sylbir
    syl
    @6
    cA
    cn
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @7
    cA
    cn
    vf
    bren
    @11
    @7
    vf
    @11
    @2
    @4
    @11
    @2
    wa
    #
    @3
    vk
    cn
    vn
    vk
    cv
    #
    @10
    ccnv
    #
    cfv
    #
    cB
    csb
    #
    ciun
    #
    @1
    @11
    @3
    @17
    wceq
    @2
    @11
    vx
    @3
    @17
    @11
    vx
    cv
    #
    cB
    wcel
    #
    vn
    cA
    wrex
    #
    @18
    @16
    wcel
    #
    vk
    cn
    wrex
    #
    @18
    @3
    wcel
    @18
    @17
    wcel
    @11
    @20
    @22
    @11
    @19
    @22
    vn
    cA
    @11
    vn
    nfv
    @21
    vn
    vk
    cn
    vn
    cn
    nfcv
    vn
    vx
    @16
    vn
    @15
    cB
    nfcsb1v
    nfcri
    #
    nfrex
    @11
    vn
    cv
    #
    cA
    wcel
    #
    @19
    @22
    @11
    @25
    @19
    w3a
    #
    @24
    @10
    cfv
    #
    cn
    wcel
    #
    @18
    vn
    @27
    @14
    cfv
    #
    cB
    csb
    #
    wcel
    #
    @22
    @11
    @25
    @28
    @19
    @11
    cA
    cn
    @24
    @10
    cA
    cn
    @10
    f1of
    ffvelrnda
    3adant3
    @26
    @18
    cB
    @30
    @11
    @25
    @19
    simp3
    @26
    @24
    @29
    wceq
    cB
    @30
    wceq
    @26
    @29
    @24
    @11
    @25
    @29
    @24
    wceq
    @19
    cA
    cn
    @24
    @10
    f1ocnvfv1
    3adant3
    eqcomd
    vn
    @29
    cB
    csbeq1a
    syl
    eleqtrd
    @21
    @31
    vk
    @27
    cn
    @13
    @27
    wceq
    #
    @16
    @30
    @18
    @32
    vn
    @15
    @29
    cB
    @13
    @27
    @14
    fveq2
    csbeq1d
    eleq2d
    rspcev
    syl2anc
    3exp
    rexlimd
    @11
    @21
    @20
    vk
    cn
    @11
    @13
    cn
    wcel
    #
    wa
    #
    @15
    cA
    wcel
    #
    @21
    @20
    wi
    cA
    cn
    @13
    @10
    f1ocnvdm
    #
    @35
    @21
    @20
    @19
    @21
    vn
    @15
    cA
    @23
    @24
    @15
    wceq
    cB
    @16
    @18
    vn
    @15
    cB
    csbeq1a
    eleq2d
    rspce
    ex
    syl
    rexlimdva
    impbid
    vn
    @18
    cA
    cB
    eliun
    vk
    @18
    cn
    @16
    eliun
    3bitr4g
    eqrdv
    adantr
    @12
    @16
    @1
    wcel
    #
    vk
    cn
    wral
    @17
    @1
    wcel
    @12
    @37
    vk
    cn
    @11
    @33
    @2
    @37
    @34
    @35
    @2
    @37
    @36
    vn
    @15
    cA
    cB
    @1
    rspcsbela
    sylan
    an32s
    ralrimiva
    @16
    vk
    iunmbl
    syl
    eqeltrd
    ex
    exlimiv
    sylbi
    jaoi
    sylbi
    imp
end
