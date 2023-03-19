include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdiv.mm"
include "cmo.mm"
include "clt.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wrex.mm"
include "c4.mm"
include "cfl.mm"
include "cfv.mm"
include "caddc.mm"
include "cz.mm"
include "cuz.mm"
include "wss.mm"
include "wb.mm"
include "cn.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "ad2antrr.mm"
include "4nn.mm"
include "jctir.mm"
include "fldivnn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "elnnuz.mm"
include "sylib.mm"
include "fzss1.mm"
include "rexss.mm"
include "ancom.mm"
include "cle.mm"
include "syl.mm"
include "nn0zd.mm"
include "elfzelz.mm"
include "zltp1le.mm"
include "syl2an.mm"
include "bicomd.mm"
include "anbi1d.mm"
include "adantl.mm"
include "peano2zd.mm"
include "adantr.mm"
include "prmz.mm"
include "oddm1d2.mm"
include "biimpa.mm"
include "elfz.mm"
include "syl3anc.mm"
include "elfzle2.mm"
include "biantrud.mm"
include "3bitr4d.mm"
include "2lgslem1a2.mm"
include "bitrd.mm"
include "wral.mm"
include "2lgslem1a1.mm"
include "sylan.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "breq2d.mm"
include "eqcomd.mm"
include "sylan9bb.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "rabbidva.mm"

theorem 2lgslem1a
  let vx: setvar x
  let cP: class P
  let vi: setvar i
  let vk: setvar k

  disjoint P i
  disjoint P x
  disjoint i x
  disjoint P k
  disjoint i k
  disjoint k x
  assert |- ( ( P e. Prime /\ -. 2 || P ) -> { x e. ZZ | E. i e. ( 1 ... ( ( P - 1 ) / 2 ) ) ( x = ( i x. 2 ) /\ ( P / 2 ) < ( x mod P ) ) } = { x e. ZZ | E. i e. ( ( ( |_ ` ( P / 4 ) ) + 1 ) ... ( ( P - 1 ) / 2 ) ) x = ( i x. 2 ) } )

  proof
    cP
    cprime
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    vx
    cv
    #
    vi
    cv
    #
    c2
    cmul
    co
    #
    wceq
    #
    cP
    c2
    cdiv
    co
    #
    @3
    cP
    cmo
    co
    #
    clt
    wbr
    #
    wa
    #
    vi
    c1
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cfz
    co
    #
    wrex
    #
    @6
    vi
    cP
    c4
    cdiv
    co
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    @11
    cfz
    co
    #
    wrex
    #
    vx
    cz
    @2
    @3
    cz
    wcel
    #
    wa
    #
    @17
    @13
    @19
    @17
    @4
    @16
    wcel
    #
    @6
    wa
    #
    vi
    @12
    wrex
    #
    @13
    @19
    @15
    c1
    cuz
    cfv
    wcel
    #
    @16
    @12
    wss
    @17
    @22
    wb
    @19
    @15
    cn
    wcel
    #
    @23
    @19
    cP
    cn0
    wcel
    #
    c4
    cn
    wcel
    #
    wa
    #
    @14
    cn0
    wcel
    #
    @24
    @19
    @25
    @26
    @0
    @25
    @1
    @18
    @0
    cP
    cP
    prmnn
    #
    nnnn0d
    #
    ad2antrr
    4nn
    jctir
    cP
    c4
    fldivnn0
    #
    @14
    nn0p1nn
    3syl
    @15
    elnnuz
    sylib
    @15
    c1
    @11
    fzss1
    @6
    vi
    @16
    @12
    rexss
    3syl
    @19
    @21
    @10
    vi
    @12
    @21
    @6
    @20
    wa
    @19
    @4
    @12
    wcel
    #
    wa
    #
    @10
    @20
    @6
    ancom
    @33
    @6
    @20
    @9
    @33
    @20
    @7
    @5
    cP
    cmo
    co
    #
    clt
    wbr
    #
    @6
    @9
    @33
    @20
    @7
    @5
    clt
    wbr
    #
    @35
    @33
    @20
    @14
    @4
    clt
    wbr
    #
    @36
    @33
    @15
    @4
    cle
    wbr
    #
    @4
    @11
    cle
    wbr
    #
    wa
    #
    @37
    @39
    wa
    @20
    @37
    @33
    @38
    @37
    @39
    @33
    @37
    @38
    @19
    @14
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @37
    @38
    wb
    @32
    @0
    @41
    @1
    @18
    @0
    @14
    @0
    @27
    @28
    @0
    @25
    @26
    @30
    4nn
    jctir
    @31
    syl
    nn0zd
    #
    ad2antrr
    @4
    c1
    @11
    elfzelz
    #
    @14
    @4
    zltp1le
    syl2an
    bicomd
    anbi1d
    @33
    @42
    @15
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @20
    @40
    wb
    @32
    @42
    @19
    @44
    adantl
    @2
    @45
    @18
    @32
    @0
    @45
    @1
    @0
    @14
    @43
    peano2zd
    adantr
    ad2antrr
    @2
    @46
    @18
    @32
    @0
    @1
    @46
    @0
    cP
    cz
    wcel
    #
    @1
    @46
    wb
    cP
    prmz
    #
    cP
    oddm1d2
    syl
    biimpa
    ad2antrr
    @4
    @15
    @11
    elfz
    syl3anc
    @33
    @39
    @37
    @32
    @39
    @19
    @4
    c1
    @11
    elfzle2
    adantl
    biantrud
    3bitr4d
    @19
    @47
    @42
    @37
    @36
    wb
    @32
    @0
    @47
    @1
    @18
    @48
    ad2antrr
    @44
    @4
    cP
    2lgslem1a2
    syl2an
    bitrd
    @33
    @5
    @34
    @7
    clt
    @19
    vk
    cv
    #
    c2
    cmul
    co
    #
    @50
    cP
    cmo
    co
    #
    wceq
    #
    vk
    @12
    wral
    #
    @32
    @5
    @34
    wceq
    #
    @2
    @53
    @18
    @0
    cP
    cn
    wcel
    @1
    @53
    @29
    cP
    vk
    2lgslem1a1
    sylan
    adantr
    @52
    @54
    vk
    @4
    @12
    vk
    vi
    weq
    #
    @50
    @5
    @51
    @34
    @49
    @4
    c2
    cmul
    oveq1
    #
    @55
    @50
    @5
    cP
    cmo
    @56
    oveq1d
    eqeq12d
    rspccva
    sylan
    breq2d
    bitrd
    @6
    @34
    @8
    @7
    clt
    @6
    @8
    @34
    @3
    @5
    cP
    cmo
    oveq1
    eqcomd
    breq2d
    sylan9bb
    pm5.32da
    syl5bb
    rexbidva
    bitrd
    bicomd
    rabbidva
end
