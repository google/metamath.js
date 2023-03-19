include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "cc0.mm"
include "wa.mm"
include "simp1.mm"
include "2re.mm"
include "peano2rem.mm"
include "remulcl.mm"
include "sylancr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "0le2.mm"
include "wi.mm"
include "0re.mm"
include "letr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imp.mm"
include "caddc.mm"
include "wb.mm"
include "resubcl.mm"
include "mpan2.mm"
include "leadd2.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "biimpa.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "2cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "subdi.mm"
include "mp3an13.mm"
include "2times.mm"
include "2t1e2.mm"
include "a1i.mm"
include "oveq12d.mm"
include "addsub.mm"
include "mp3an3.mm"
include "anidms.mm"
include "3eqtrrd.mm"
include "syl.mm"
include "3brtr3d.mm"
include "jca.mm"
include "3adant2.mm"
include "leexp1a.mm"
include "syl31anc.mm"
include "recnd.mm"
include "mulexp.mm"
include "sylan.mm"
include "3adant3.mm"
include "breqtrd.mm"

theorem expubnd
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. NN0 /\ 2 <_ A ) -> ( A ^ N ) <_ ( ( 2 ^ N ) x. ( ( A - 1 ) ^ N ) ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    c2
    cA
    cle
    wbr
    #
    w3a
    #
    cA
    cN
    cexp
    co
    #
    c2
    cA
    c1
    cmin
    co
    #
    cmul
    co
    #
    cN
    cexp
    co
    #
    c2
    cN
    cexp
    co
    @5
    cN
    cexp
    co
    cmul
    co
    #
    cle
    @3
    @0
    @6
    cr
    wcel
    #
    @1
    cc0
    cA
    cle
    wbr
    #
    cA
    @6
    cle
    wbr
    #
    wa
    #
    @4
    @7
    cle
    wbr
    @0
    @1
    @2
    simp1
    @0
    @1
    @9
    @2
    @0
    c2
    cr
    wcel
    #
    @5
    cr
    wcel
    @9
    2re
    cA
    peano2rem
    #
    c2
    @5
    remulcl
    sylancr
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @12
    @1
    @0
    @2
    wa
    #
    @10
    @11
    @0
    @2
    @10
    @0
    cc0
    c2
    cle
    wbr
    #
    @2
    @10
    0le2
    cc0
    cr
    wcel
    @13
    @0
    @16
    @2
    wa
    @10
    wi
    0re
    2re
    cc0
    c2
    cA
    letr
    mp3an12
    mpani
    imp
    @15
    cA
    c2
    cmin
    co
    #
    c2
    caddc
    co
    #
    @17
    cA
    caddc
    co
    #
    cA
    @6
    cle
    @0
    @2
    @18
    @19
    cle
    wbr
    #
    @0
    @17
    cr
    wcel
    #
    @2
    @20
    wb
    #
    @0
    @13
    @21
    2re
    cA
    c2
    resubcl
    mpan2
    @13
    @0
    @21
    @22
    2re
    c2
    cA
    @17
    leadd2
    mp3an1
    mpdan
    biimpa
    @0
    @18
    cA
    wceq
    #
    @2
    @0
    cA
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    @23
    cA
    recn
    #
    2cn
    cA
    c2
    npcan
    sylancl
    adantr
    @0
    @19
    @6
    wceq
    #
    @2
    @0
    @24
    @27
    @26
    @24
    @6
    c2
    cA
    cmul
    co
    #
    c2
    c1
    cmul
    co
    #
    cmin
    co
    #
    cA
    cA
    caddc
    co
    #
    c2
    cmin
    co
    #
    @19
    @25
    @24
    c1
    cc
    wcel
    @6
    @30
    wceq
    2cn
    ax-1cn
    c2
    cA
    c1
    subdi
    mp3an13
    @24
    @28
    @31
    @29
    c2
    cmin
    cA
    2times
    @29
    c2
    wceq
    @24
    2t1e2
    a1i
    oveq12d
    @24
    @32
    @19
    wceq
    #
    @24
    @24
    @25
    @33
    2cn
    cA
    cA
    c2
    addsub
    mp3an3
    anidms
    3eqtrrd
    syl
    adantr
    3brtr3d
    jca
    3adant2
    cA
    @6
    cN
    leexp1a
    syl31anc
    @0
    @1
    @7
    @8
    wceq
    #
    @2
    @0
    @5
    cc
    wcel
    #
    @1
    @34
    @0
    @5
    @14
    recnd
    @25
    @35
    @1
    @34
    2cn
    c2
    @5
    cN
    mulexp
    mp3an1
    sylan
    3adant3
    breqtrd
end
