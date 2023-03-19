include "cprime.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cpc.mm"
include "prmnn.mm"
include "adantr.mm"
include "elfznn0.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "prmz.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "elfzuz3.mm"
include "dvdsexp.mm"
include "syl3anc.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "cle.mm"
include "simpl.mm"
include "elrabi.mm"
include "pccl.mm"
include "nnzd.mm"
include "simplr.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "simprbi.mm"
include "pcdvdstr.mm"
include "syl13anc.mm"
include "wceq.mm"
include "pcidlem.mm"
include "breqtrd.mm"
include "wb.mm"
include "fznn0.mm"
include "syl.mm"
include "mpbir2and.mm"
include "wrex.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "pcprmpw2.mm"
include "mpbid.mm"
include "adantrl.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "elfzelz.mm"
include "pcid.mm"
include "eqcomd.mm"
include "adantrr.mm"
include "impbid.mm"
include "f1o2d.mm"

theorem dvdsppwf1o
  let vx: setvar x
  let cA: class A
  let cP: class P
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  assume dvdsppwf1o.f: |- F = ( n e. ( 0 ... A ) |-> ( P ^ n ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint P n
  disjoint P x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint P m
  assert |- ( ( P e. Prime /\ A e. NN0 ) -> F : ( 0 ... A ) -1-1-onto-> { x e. NN | x || ( P ^ A ) } )

  proof
    cP
    cprime
    wcel
    #
    cA
    cn0
    wcel
    #
    wa
    #
    vn
    vm
    cc0
    cA
    cfz
    co
    #
    vx
    cv
    #
    cP
    cA
    cexp
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    cP
    vn
    cv
    #
    cexp
    co
    #
    cP
    vm
    cv
    #
    cpc
    co
    #
    cF
    dvdsppwf1o.f
    @2
    @8
    @3
    wcel
    #
    wa
    #
    @9
    cn
    wcel
    #
    @9
    @5
    cdvds
    wbr
    #
    @9
    @7
    wcel
    @2
    cP
    cn
    wcel
    #
    @8
    cn0
    wcel
    #
    @14
    @12
    @0
    @16
    @1
    cP
    prmnn
    adantr
    @8
    cA
    elfznn0
    #
    cP
    @8
    nnexpcl
    syl2an
    @13
    cP
    cz
    wcel
    #
    @17
    cA
    @8
    cuz
    cfv
    wcel
    #
    @15
    @0
    @19
    @1
    @12
    cP
    prmz
    #
    ad2antrr
    @12
    @17
    @2
    @18
    adantl
    @12
    @20
    @2
    @8
    cc0
    cA
    elfzuz3
    adantl
    cP
    @8
    cA
    dvdsexp
    syl3anc
    @6
    @15
    vx
    @9
    cn
    @4
    @9
    @5
    cdvds
    breq1
    elrab
    sylanbrc
    @2
    @10
    @7
    wcel
    #
    wa
    #
    @11
    @3
    wcel
    #
    @11
    cn0
    wcel
    #
    @11
    cA
    cle
    wbr
    #
    @2
    @0
    @10
    cn
    wcel
    #
    @25
    @22
    @0
    @1
    simpl
    #
    @6
    vx
    @10
    cn
    elrabi
    #
    cP
    @10
    pccl
    syl2an
    @23
    @11
    cP
    @5
    cpc
    co
    #
    cA
    cle
    @23
    @0
    @10
    cz
    wcel
    @5
    cz
    wcel
    #
    @10
    @5
    cdvds
    wbr
    #
    @11
    @30
    cle
    wbr
    @2
    @0
    @22
    @28
    adantr
    @23
    @10
    @22
    @27
    @2
    @29
    adantl
    nnzd
    @23
    @19
    @1
    @31
    @0
    @19
    @1
    @22
    @21
    ad2antrr
    @0
    @1
    @22
    simplr
    #
    cP
    cA
    zexpcl
    syl2anc
    @22
    @32
    @2
    @22
    @27
    @32
    @6
    @32
    vx
    @10
    cn
    @4
    @10
    @5
    cdvds
    breq1
    elrab
    simprbi
    adantl
    #
    @10
    @5
    cP
    pcdvdstr
    syl13anc
    @2
    @30
    cA
    wceq
    @22
    cA
    cP
    pcidlem
    adantr
    breqtrd
    @23
    @1
    @24
    @25
    @26
    wa
    wb
    @33
    @11
    cA
    fznn0
    syl
    mpbir2and
    @2
    @12
    @22
    wa
    wa
    #
    @8
    @11
    wceq
    #
    @10
    @9
    wceq
    #
    @35
    @37
    @36
    @10
    cP
    @11
    cexp
    co
    #
    wceq
    #
    @2
    @22
    @39
    @12
    @23
    @10
    @9
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @39
    @23
    @1
    @32
    @41
    @33
    @34
    @40
    @32
    vn
    cA
    cn0
    @8
    cA
    wceq
    @9
    @5
    @10
    cdvds
    @8
    cA
    cP
    cexp
    oveq2
    breq2d
    rspcev
    syl2anc
    @2
    @0
    @27
    @41
    @39
    wb
    @22
    @28
    @29
    @10
    cP
    vn
    pcprmpw2
    syl2an
    mpbid
    adantrl
    @36
    @9
    @38
    @10
    @8
    @11
    cP
    cexp
    oveq2
    eqeq2d
    syl5ibrcom
    @35
    @36
    @37
    @8
    cP
    @9
    cpc
    co
    #
    wceq
    #
    @2
    @12
    @43
    @22
    @13
    @42
    @8
    @2
    @0
    @8
    cz
    wcel
    @42
    @8
    wceq
    @12
    @28
    @8
    cc0
    cA
    elfzelz
    @8
    cP
    pcid
    syl2an
    eqcomd
    adantrr
    @37
    @11
    @42
    @8
    @10
    @9
    cP
    cpc
    oveq2
    eqeq2d
    syl5ibrcom
    impbid
    f1o2d
end
