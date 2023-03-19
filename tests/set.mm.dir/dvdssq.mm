include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "cc0.mm"
include "wceq.mm"
include "breq1.mm"
include "sq0i.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "cn.mm"
include "nnabscl.mm"
include "breq2.mm"
include "breq2d.mm"
include "dvdssqlem.mm"
include "sylan2.mm"
include "nnz.mm"
include "simpl.mm"
include "dvdsabsb.mm"
include "syl2an.mm"
include "nnsqcl.mm"
include "nnzd.mm"
include "zsqcl.mm"
include "adantr.mm"
include "cc.mm"
include "zcn.mm"
include "abssq.mm"
include "syl.mm"
include "adantl.mm"
include "bitr4d.mm"
include "3bitr4d.mm"
include "anassrs.mm"
include "dvds0.mm"
include "2thd.mm"
include "pm2.61ne.mm"
include "sylan.mm"
include "absdvdsb.mm"
include "adantlr.mm"
include "eqcomd.mm"
include "bitrd.mm"
include "an32s.mm"
include "0dvds.mm"
include "sqeq0.mm"

theorem dvdssq
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> ( M ^ 2 ) || ( N ^ 2 ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cM
    cN
    cdvds
    wbr
    #
    cM
    c2
    cexp
    co
    #
    cN
    c2
    cexp
    co
    #
    cdvds
    wbr
    #
    wb
    #
    cc0
    cN
    cdvds
    wbr
    #
    cc0
    @4
    cdvds
    wbr
    #
    wb
    #
    cM
    cc0
    cM
    cc0
    wceq
    #
    @2
    @7
    @5
    @8
    cM
    cc0
    cN
    cdvds
    breq1
    @10
    @3
    cc0
    @4
    cdvds
    cM
    sq0i
    breq1d
    bibi12d
    @0
    cM
    cc0
    wne
    #
    @1
    @6
    @0
    @11
    wa
    #
    @1
    wa
    #
    cM
    cabs
    cfv
    #
    cN
    cdvds
    wbr
    #
    @14
    c2
    cexp
    co
    #
    @4
    cdvds
    wbr
    #
    @2
    @5
    @12
    @14
    cn
    wcel
    #
    @1
    @15
    @17
    wb
    #
    cM
    nnabscl
    @18
    @1
    wa
    @19
    @14
    cc0
    cdvds
    wbr
    #
    @16
    cc0
    cdvds
    wbr
    #
    wb
    #
    cN
    cc0
    cN
    cc0
    wceq
    #
    @15
    @20
    @17
    @21
    cN
    cc0
    @14
    cdvds
    breq2
    @23
    @4
    cc0
    @16
    cdvds
    cN
    sq0i
    breq2d
    bibi12d
    @18
    @1
    cN
    cc0
    wne
    #
    @19
    @18
    @1
    @24
    wa
    #
    wa
    #
    @14
    cN
    cabs
    cfv
    #
    cdvds
    wbr
    #
    @16
    @27
    c2
    cexp
    co
    #
    cdvds
    wbr
    #
    @15
    @17
    @25
    @18
    @27
    cn
    wcel
    @28
    @30
    wb
    cN
    nnabscl
    @14
    @27
    dvdssqlem
    sylan2
    @18
    @14
    cz
    wcel
    #
    @1
    @15
    @28
    wb
    @25
    @14
    nnz
    #
    @1
    @24
    simpl
    @14
    cN
    dvdsabsb
    syl2an
    @26
    @17
    @16
    @4
    cabs
    cfv
    #
    cdvds
    wbr
    #
    @30
    @18
    @16
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @17
    @34
    wb
    @25
    @18
    @16
    @14
    nnsqcl
    nnzd
    @1
    @36
    @24
    cN
    zsqcl
    #
    adantr
    @16
    @4
    dvdsabsb
    syl2an
    @25
    @30
    @34
    wb
    @18
    @25
    @29
    @33
    @16
    cdvds
    @25
    cN
    cc
    wcel
    #
    @29
    @33
    wceq
    @1
    @38
    @24
    cN
    zcn
    #
    adantr
    cN
    abssq
    syl
    breq2d
    adantl
    bitr4d
    3bitr4d
    anassrs
    @18
    @22
    @1
    @18
    @31
    @22
    @32
    @31
    @20
    @21
    @14
    dvds0
    @31
    @35
    @21
    @14
    zsqcl
    @16
    dvds0
    syl
    2thd
    syl
    adantr
    pm2.61ne
    sylan
    @0
    @1
    @2
    @15
    wb
    @11
    cM
    cN
    absdvdsb
    adantlr
    @13
    @5
    @3
    cabs
    cfv
    #
    @4
    cdvds
    wbr
    #
    @17
    @12
    @3
    cz
    wcel
    #
    @36
    @5
    @41
    wb
    @1
    @0
    @42
    @11
    cM
    zsqcl
    adantr
    @37
    @3
    @4
    absdvdsb
    syl2an
    @12
    @41
    @17
    wb
    @1
    @12
    @40
    @16
    @4
    cdvds
    @0
    @40
    @16
    wceq
    @11
    @0
    @16
    @40
    @0
    cM
    cc
    wcel
    @16
    @40
    wceq
    cM
    zcn
    cM
    abssq
    syl
    eqcomd
    adantr
    breq1d
    adantr
    bitrd
    3bitr4d
    an32s
    @1
    @9
    @0
    @1
    @7
    @4
    cc0
    wceq
    #
    @8
    @1
    @7
    @23
    @43
    cN
    0dvds
    @1
    @38
    @43
    @23
    wb
    @39
    cN
    sqeq0
    syl
    bitr4d
    @1
    @36
    @8
    @43
    wb
    @37
    @4
    0dvds
    syl
    bitr4d
    adantl
    pm2.61ne
end
