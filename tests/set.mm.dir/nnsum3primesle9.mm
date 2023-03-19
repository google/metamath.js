include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c8.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "c3.mm"
include "wo.mm"
include "c4.mm"
include "c5.mm"
include "c6.mm"
include "c7.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cprime.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "clt.mm"
include "eluzelre.mm"
include "cr.mm"
include "8re.mm"
include "a1i.mm"
include "leloed.mm"
include "caddc.mm"
include "cz.mm"
include "wb.mm"
include "eluzelz.mm"
include "7nn.mm"
include "nnzi.mm"
include "zleltp1.mm"
include "sylancl.mm"
include "7re.mm"
include "7p1e8.mm"
include "breq2i.mm"
include "3bitr3rd.mm"
include "6nn.mm"
include "6re.mm"
include "6p1e7.mm"
include "5nn.mm"
include "5re.mm"
include "5p1e6.mm"
include "4z.mm"
include "4re.mm"
include "4p1e5.mm"
include "3z.mm"
include "3re.mm"
include "3p1e4.mm"
include "w3a.mm"
include "eluz2.mm"
include "wi.mm"
include "2re.mm"
include "zre.mm"
include "cmin.mm"
include "3m1e2.mm"
include "eqcomi.mm"
include "breq1i.mm"
include "zlem1lt.mm"
include "mpan.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "wn.mm"
include "lenltd.mm"
include "pm2.21.mm"
include "syl6bi.mm"
include "syldc.mm"
include "eqcom.mm"
include "biimpi.mm"
include "2a1d.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"
include "2lt3.mm"
include "breq1.mm"
include "mpbiri.mm"
include "impbid1.mm"
include "3adant1.mm"
include "sylbi.mm"
include "orbi1d.mm"
include "bitrd.mm"
include "biimpd.mm"
include "2prm.mm"
include "eleq1.mm"
include "nnsum3primesprm.mm"
include "syl.mm"
include "3prm.mm"
include "nnsum3primes4.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "5prm.mm"
include "cgbe.mm"
include "6gbe.mm"
include "nnsum3primesgbe.mm"
include "7prm.mm"
include "8gbe.mm"

theorem nnsum3primesle9
  let vf: setvar f
  let vk: setvar k
  let cN: class N
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x

  disjoint N d
  disjoint N f
  disjoint N k
  disjoint d f
  disjoint d k
  disjoint f k
  disjoint N p
  disjoint N q
  disjoint d p
  disjoint d q
  disjoint f p
  disjoint f q
  disjoint k p
  disjoint k q
  disjoint p q
  disjoint k x
  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ N <_ 8 ) -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 3 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    c8
    cle
    wbr
    #
    wa
    cN
    c2
    wceq
    #
    cN
    c3
    wceq
    #
    wo
    #
    cN
    c4
    wceq
    #
    wo
    #
    cN
    c5
    wceq
    #
    wo
    #
    cN
    c6
    wceq
    #
    wo
    #
    cN
    c7
    wceq
    #
    wo
    #
    cN
    c8
    wceq
    #
    wo
    #
    vd
    cv
    #
    c3
    cle
    wbr
    #
    cN
    c1
    @15
    cfz
    co
    #
    vk
    cv
    vf
    cv
    cfv
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @17
    cmap
    co
    #
    wrex
    vd
    cn
    wrex
    #
    @0
    @1
    @14
    @0
    @1
    cN
    c8
    clt
    wbr
    #
    @13
    wo
    #
    @14
    @0
    cN
    c8
    c2
    cN
    eluzelre
    #
    c8
    cr
    wcel
    @0
    8re
    a1i
    leloed
    @0
    @24
    @14
    @0
    @23
    @12
    @13
    @0
    @23
    cN
    c7
    clt
    wbr
    #
    @11
    wo
    #
    @12
    @0
    cN
    c7
    cle
    wbr
    #
    cN
    c7
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @27
    @23
    @0
    cN
    cz
    wcel
    #
    c7
    cz
    wcel
    @28
    @30
    wb
    c2
    cN
    eluzelz
    #
    c7
    7nn
    nnzi
    cN
    c7
    zleltp1
    sylancl
    @0
    cN
    c7
    @25
    c7
    cr
    wcel
    @0
    7re
    a1i
    leloed
    @30
    @23
    wb
    @0
    @29
    c8
    cN
    clt
    7p1e8
    breq2i
    a1i
    3bitr3rd
    @0
    @26
    @10
    @11
    @0
    @26
    cN
    c6
    clt
    wbr
    #
    @9
    wo
    #
    @10
    @0
    cN
    c6
    cle
    wbr
    #
    cN
    c6
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @34
    @26
    @0
    @31
    c6
    cz
    wcel
    @35
    @37
    wb
    @32
    c6
    6nn
    nnzi
    cN
    c6
    zleltp1
    sylancl
    @0
    cN
    c6
    @25
    c6
    cr
    wcel
    @0
    6re
    a1i
    leloed
    @37
    @26
    wb
    @0
    @36
    c7
    cN
    clt
    6p1e7
    breq2i
    a1i
    3bitr3rd
    @0
    @33
    @8
    @9
    @0
    @33
    cN
    c5
    clt
    wbr
    #
    @7
    wo
    #
    @8
    @0
    cN
    c5
    cle
    wbr
    #
    cN
    c5
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @39
    @33
    @0
    @31
    c5
    cz
    wcel
    @40
    @42
    wb
    @32
    c5
    5nn
    nnzi
    cN
    c5
    zleltp1
    sylancl
    @0
    cN
    c5
    @25
    c5
    cr
    wcel
    @0
    5re
    a1i
    leloed
    @42
    @33
    wb
    @0
    @41
    c6
    cN
    clt
    5p1e6
    breq2i
    a1i
    3bitr3rd
    @0
    @38
    @6
    @7
    @0
    @38
    cN
    c4
    clt
    wbr
    #
    @5
    wo
    #
    @6
    @0
    cN
    c4
    cle
    wbr
    #
    cN
    c4
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @44
    @38
    @0
    @31
    c4
    cz
    wcel
    @45
    @47
    wb
    @32
    4z
    cN
    c4
    zleltp1
    sylancl
    @0
    cN
    c4
    @25
    c4
    cr
    wcel
    @0
    4re
    a1i
    leloed
    @47
    @38
    wb
    @0
    @46
    c5
    cN
    clt
    4p1e5
    breq2i
    a1i
    3bitr3rd
    @0
    @43
    @4
    @5
    @0
    @43
    cN
    c3
    clt
    wbr
    #
    @3
    wo
    #
    @4
    @0
    cN
    c3
    cle
    wbr
    #
    cN
    c3
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @49
    @43
    @0
    @31
    c3
    cz
    wcel
    #
    @50
    @52
    wb
    @32
    3z
    cN
    c3
    zleltp1
    sylancl
    @0
    cN
    c3
    @25
    c3
    cr
    wcel
    #
    @0
    3re
    a1i
    leloed
    @52
    @43
    wb
    @0
    @51
    c4
    cN
    clt
    3p1e4
    breq2i
    a1i
    3bitr3rd
    @0
    @48
    @2
    @3
    @0
    c2
    cz
    wcel
    #
    @31
    c2
    cN
    cle
    wbr
    #
    w3a
    @48
    @2
    wb
    #
    c2
    cN
    eluz2
    @31
    @56
    @57
    @55
    @31
    @56
    wa
    @48
    @2
    @31
    @56
    @48
    @2
    wi
    #
    @31
    @56
    c2
    cN
    clt
    wbr
    #
    c2
    cN
    wceq
    #
    wo
    #
    @58
    @31
    c2
    cN
    c2
    cr
    wcel
    @31
    2re
    a1i
    cN
    zre
    #
    leloed
    @61
    @31
    @58
    @59
    @31
    @58
    wi
    @60
    @31
    @59
    c3
    cN
    cle
    wbr
    #
    @58
    @59
    c3
    c1
    cmin
    co
    #
    cN
    clt
    wbr
    #
    @31
    @63
    c2
    @64
    cN
    clt
    @64
    c2
    3m1e2
    eqcomi
    breq1i
    @31
    @63
    @65
    @53
    @31
    @63
    @65
    wb
    3z
    c3
    cN
    zlem1lt
    mpan
    biimprd
    syl5bi
    @31
    @63
    @48
    wn
    @58
    @31
    c3
    cN
    @54
    @31
    3re
    a1i
    @62
    lenltd
    @48
    @2
    pm2.21
    syl6bi
    syldc
    @60
    @2
    @31
    @48
    @60
    @2
    c2
    cN
    eqcom
    biimpi
    2a1d
    jaoi
    com12
    sylbid
    imp
    @2
    @48
    c2
    c3
    clt
    wbr
    2lt3
    cN
    c2
    c3
    clt
    breq1
    mpbiri
    impbid1
    3adant1
    sylbi
    orbi1d
    bitrd
    orbi1d
    bitrd
    orbi1d
    bitrd
    orbi1d
    bitrd
    orbi1d
    bitrd
    orbi1d
    biimpd
    sylbid
    imp
    @12
    @22
    @13
    @10
    @22
    @11
    @8
    @22
    @9
    @6
    @22
    @7
    @4
    @22
    @5
    @2
    @22
    @3
    @2
    cN
    cprime
    wcel
    #
    @22
    @2
    @66
    c2
    cprime
    wcel
    2prm
    cN
    c2
    cprime
    eleq1
    mpbiri
    cN
    vf
    vk
    vd
    nnsum3primesprm
    #
    syl
    @3
    @66
    @22
    @3
    @66
    c3
    cprime
    wcel
    3prm
    cN
    c3
    cprime
    eleq1
    mpbiri
    @67
    syl
    jaoi
    @5
    @22
    @16
    c4
    @18
    wceq
    #
    wa
    #
    vf
    @21
    wrex
    vd
    cn
    wrex
    vf
    vk
    vd
    nnsum3primes4
    @5
    @20
    @69
    vd
    vf
    cn
    @21
    @5
    @19
    @68
    @16
    cN
    c4
    @18
    eqeq1
    anbi2d
    2rexbidv
    mpbiri
    jaoi
    @7
    @66
    @22
    @7
    @66
    c5
    cprime
    wcel
    5prm
    cN
    c5
    cprime
    eleq1
    mpbiri
    @67
    syl
    jaoi
    @9
    cN
    cgbe
    wcel
    #
    @22
    @9
    @70
    c6
    cgbe
    wcel
    6gbe
    cN
    c6
    cgbe
    eleq1
    mpbiri
    vf
    vk
    cN
    vd
    nnsum3primesgbe
    #
    syl
    jaoi
    @11
    @66
    @22
    @11
    @66
    c7
    cprime
    wcel
    7prm
    cN
    c7
    cprime
    eleq1
    mpbiri
    @67
    syl
    jaoi
    @13
    @70
    @22
    @13
    @70
    c8
    cgbe
    wcel
    8gbe
    cN
    c8
    cgbe
    eleq1
    mpbiri
    @71
    syl
    jaoi
    syl
end
