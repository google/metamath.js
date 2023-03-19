include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cz.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cle.mm"
include "2z.mm"
include "a1i.mm"
include "wa.mm"
include "fzfid.mm"
include "cn0.mm"
include "neg1z.mm"
include "elfznn0.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "adantl.mm"
include "eluzge2nn0.mm"
include "adantr.mm"
include "nn0expcld.mm"
include "nn0zd.mm"
include "zmulcld.mm"
include "fsumzcl.mm"
include "3adant3.mm"
include "c3.mm"
include "caddc.mm"
include "cdiv.mm"
include "wceq.mm"
include "simp1.mm"
include "3z.mm"
include "eluzelz.mm"
include "3ad2ant2.mm"
include "wi.mm"
include "eluz2.mm"
include "clt.mm"
include "wo.mm"
include "cr.mm"
include "2re.mm"
include "zre.mm"
include "leloed.mm"
include "wb.mm"
include "zltp1le.mm"
include "mpan.mm"
include "biimpd.mm"
include "df-3.mm"
include "breq1i.mm"
include "syl6ibr.mm"
include "com13.mm"
include "z2even.mm"
include "breq2.mm"
include "mpbii.mm"
include "pm2.24d.mm"
include "a1d.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "syl3anbrc.mm"
include "cc.mm"
include "eluzelcn.mm"
include "3ad2ant1.mm"
include "cn.mm"
include "eluz2nn.mm"
include "simp3.mm"
include "oddpwp1fsum.mm"
include "eqcomd.mm"
include "wne.mm"
include "nn0cnd.mm"
include "peano2cn.mm"
include "syl.mm"
include "zcnd.mm"
include "peano2nnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "jca.mm"
include "divmul.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "lighneallem4a.mm"

theorem lighneallem4b
  let cA: class A
  let vk: setvar k
  let cM: class M
  let vx: setvar x

  disjoint A k
  disjoint M k
  disjoint k x
  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ( ZZ>= ` 2 ) /\ -. 2 || M ) -> sum_ k e. ( 0 ... ( M - 1 ) ) ( ( -u 1 ^ k ) x. ( A ^ k ) ) e. ( ZZ>= ` 2 ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    @0
    wcel
    #
    c2
    cM
    cdvds
    wbr
    #
    wn
    #
    w3a
    #
    c2
    cz
    wcel
    #
    cc0
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    cneg
    #
    vk
    cv
    #
    cexp
    co
    #
    cA
    @10
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cz
    wcel
    #
    c2
    @14
    cle
    wbr
    #
    @14
    @0
    wcel
    @6
    @5
    2z
    a1i
    @1
    @2
    @15
    @4
    @1
    @2
    wa
    #
    @8
    @13
    vk
    @17
    cc0
    @7
    fzfid
    @17
    @10
    @8
    wcel
    #
    wa
    #
    @11
    @12
    @18
    @11
    cz
    wcel
    #
    @17
    @18
    @9
    cz
    wcel
    @10
    cn0
    wcel
    #
    @20
    neg1z
    @10
    @7
    elfznn0
    #
    @9
    @10
    zexpcl
    sylancr
    adantl
    @19
    @12
    @19
    cA
    @10
    @17
    cA
    cn0
    wcel
    #
    @18
    @1
    @23
    @2
    cA
    eluzge2nn0
    adantr
    #
    adantr
    @18
    @21
    @17
    @22
    adantl
    nn0expcld
    nn0zd
    zmulcld
    fsumzcl
    3adant3
    #
    @5
    @1
    cM
    c3
    cuz
    cfv
    wcel
    #
    @14
    cA
    cM
    cexp
    co
    #
    c1
    caddc
    co
    #
    cA
    c1
    caddc
    co
    #
    cdiv
    co
    #
    wceq
    @16
    @1
    @2
    @4
    simp1
    @5
    c3
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    c3
    cM
    cle
    wbr
    #
    @26
    @31
    @5
    3z
    a1i
    @2
    @1
    @32
    @4
    c2
    cM
    eluzelz
    3ad2ant2
    @2
    @4
    @33
    @1
    @2
    @4
    @33
    @2
    @6
    @32
    c2
    cM
    cle
    wbr
    #
    w3a
    @4
    @33
    wi
    #
    c2
    cM
    eluz2
    @32
    @34
    @35
    @6
    @32
    @34
    @35
    @32
    @34
    c2
    cM
    clt
    wbr
    #
    c2
    cM
    wceq
    #
    wo
    #
    @35
    @32
    c2
    cM
    c2
    cr
    wcel
    @32
    2re
    a1i
    cM
    zre
    leloed
    @38
    @32
    @35
    @36
    @32
    @35
    wi
    @37
    @4
    @32
    @36
    @33
    @32
    @36
    @33
    wi
    wi
    @4
    @32
    @36
    c2
    c1
    caddc
    co
    #
    cM
    cle
    wbr
    #
    @33
    @32
    @36
    @40
    @6
    @32
    @36
    @40
    wb
    2z
    c2
    cM
    zltp1le
    mpan
    biimpd
    c3
    @39
    cM
    cle
    df-3
    breq1i
    syl6ibr
    a1i
    com13
    @37
    @35
    @32
    @37
    @3
    @33
    @37
    c2
    c2
    cdvds
    wbr
    @3
    z2even
    c2
    cM
    c2
    cdvds
    breq2
    mpbii
    pm2.24d
    a1d
    jaoi
    com12
    sylbid
    imp
    3adant1
    sylbi
    imp
    3adant1
    c3
    cM
    eluz2
    syl3anbrc
    @5
    @30
    @14
    @5
    @30
    @14
    wceq
    #
    @29
    @14
    cmul
    co
    #
    @28
    wceq
    #
    @5
    @28
    @42
    @5
    cA
    vk
    cM
    @1
    @2
    cA
    cc
    wcel
    @4
    c2
    cA
    eluzelcn
    3ad2ant1
    @2
    @1
    cM
    cn
    wcel
    @4
    cM
    eluz2nn
    3ad2ant2
    @1
    @2
    @4
    simp3
    oddpwp1fsum
    eqcomd
    @5
    @28
    cc
    wcel
    #
    @14
    cc
    wcel
    @29
    cc
    wcel
    #
    @29
    cc0
    wne
    #
    wa
    #
    @41
    @43
    wb
    @1
    @2
    @44
    @4
    @17
    @27
    cc
    wcel
    @44
    @17
    @27
    @17
    cA
    cM
    @24
    @2
    cM
    cn0
    wcel
    @1
    cM
    eluzge2nn0
    adantl
    nn0expcld
    nn0cnd
    @27
    peano2cn
    syl
    3adant3
    @5
    @14
    @25
    zcnd
    @1
    @2
    @47
    @4
    @1
    @45
    @46
    @1
    @29
    @1
    cA
    cA
    eluz2nn
    peano2nnd
    #
    nncnd
    @1
    @29
    @48
    nnne0d
    jca
    3ad2ant1
    @28
    @14
    @29
    divmul
    syl3anc
    mpbird
    eqcomd
    cA
    @14
    cM
    lighneallem4a
    syl3anc
    c2
    @14
    eluz2
    syl3anbrc
end
