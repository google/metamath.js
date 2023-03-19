include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "cc0.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2.mm"
include "breq12d.mm"
include "c0.mm"
include "0ex.mm"
include "enref.mm"
include "fz10.mm"
include "com.mm"
include "cuz.mm"
include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "0z.mm"
include "om2uzf1oi.mm"
include "peano1.mm"
include "pm3.2i.mm"
include "om2uz0i.mm"
include "f1ocnvfv.mm"
include "mp2.mm"
include "3brtr4i.mm"
include "cn0.mm"
include "csn.mm"
include "cun.mm"
include "cin.mm"
include "simpr.mm"
include "cvv.mm"
include "ovex.mm"
include "fvex.mm"
include "en2sn.mm"
include "mp2an.mm"
include "a1i.mm"
include "fzp1disj.mm"
include "wn.mm"
include "word.mm"
include "f1ocnvdm.mm"
include "mpan.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "nnord.mm"
include "ordirr.mm"
include "3syl.mm"
include "adantr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "unen.mm"
include "syl22anc.mm"
include "cz.mm"
include "cmin.mm"
include "1z.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "fzsuc2.mm"
include "sylancr.mm"
include "csuc.mm"
include "peano2.mm"
include "syl.mm"
include "jctil.mm"
include "om2uzsuci.mm"
include "f1ocnvfv2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "sylc.mm"
include "df-suc.mm"
include "syl6eq.mm"
include "3brtr4d.mm"
include "ex.mm"
include "nn0ind.mm"

theorem fzennn
  let vx: setvar x
  let cG: class G
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume fzennn.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )


  assert |- ( N e. NN0 -> ( 1 ... N ) ~~ ( `' G ` N ) )

  proof
    c1
    vn
    cv
    #
    cfz
    co
    #
    @0
    cG
    ccnv
    #
    cfv
    #
    cen
    wbr
    c1
    cc0
    cfz
    co
    #
    cc0
    @2
    cfv
    #
    cen
    wbr
    c1
    vm
    cv
    #
    cfz
    co
    #
    @6
    @2
    cfv
    #
    cen
    wbr
    #
    c1
    @6
    c1
    caddc
    co
    #
    cfz
    co
    #
    @10
    @2
    cfv
    #
    cen
    wbr
    #
    c1
    cN
    cfz
    co
    #
    cN
    @2
    cfv
    #
    cen
    wbr
    vn
    vm
    cN
    @0
    cc0
    wceq
    @1
    @4
    @3
    @5
    cen
    @0
    cc0
    c1
    cfz
    oveq2
    @0
    cc0
    @2
    fveq2
    breq12d
    @0
    @6
    wceq
    @1
    @7
    @3
    @8
    cen
    @0
    @6
    c1
    cfz
    oveq2
    @0
    @6
    @2
    fveq2
    breq12d
    @0
    @10
    wceq
    @1
    @11
    @3
    @12
    cen
    @0
    @10
    c1
    cfz
    oveq2
    @0
    @10
    @2
    fveq2
    breq12d
    @0
    cN
    wceq
    @1
    @14
    @3
    @15
    cen
    @0
    cN
    c1
    cfz
    oveq2
    @0
    cN
    @2
    fveq2
    breq12d
    c0
    c0
    @4
    @5
    cen
    c0
    0ex
    enref
    fz10
    com
    cc0
    cuz
    cfv
    #
    cG
    wf1o
    #
    c0
    com
    wcel
    #
    wa
    c0
    cG
    cfv
    cc0
    wceq
    @5
    c0
    wceq
    @17
    @18
    vx
    cc0
    cG
    0z
    fzennn.1
    om2uzf1oi
    #
    peano1
    pm3.2i
    vx
    cc0
    cG
    0z
    fzennn.1
    om2uz0i
    com
    @16
    c0
    cc0
    cG
    f1ocnvfv
    mp2
    3brtr4i
    @6
    cn0
    wcel
    #
    @9
    @13
    @20
    @9
    wa
    #
    @7
    @10
    csn
    #
    cun
    #
    @8
    @8
    csn
    #
    cun
    #
    @11
    @12
    cen
    @21
    @9
    @22
    @24
    cen
    wbr
    #
    @7
    @22
    cin
    c0
    wceq
    #
    @8
    @24
    cin
    c0
    wceq
    #
    @23
    @25
    cen
    wbr
    @20
    @9
    simpr
    @26
    @21
    @10
    cvv
    wcel
    @8
    cvv
    wcel
    @26
    @6
    c1
    caddc
    ovex
    @6
    @2
    fvex
    @10
    @8
    cvv
    cvv
    en2sn
    mp2an
    a1i
    @27
    @21
    c1
    @6
    fzp1disj
    a1i
    @21
    @8
    @8
    wcel
    wn
    #
    @28
    @20
    @29
    @9
    @20
    @8
    com
    wcel
    #
    @8
    word
    @29
    @30
    @6
    @16
    cn0
    @17
    @6
    @16
    wcel
    #
    @30
    @19
    com
    @16
    @6
    cG
    f1ocnvdm
    mpan
    nn0uz
    eleq2s
    #
    @8
    nnord
    @8
    ordirr
    3syl
    adantr
    @8
    @8
    disjsn
    sylibr
    @7
    @8
    @22
    @24
    unen
    syl22anc
    @20
    @11
    @23
    wceq
    #
    @9
    @20
    c1
    cz
    wcel
    @6
    c1
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @33
    1z
    @20
    @36
    cn0
    @35
    @6
    cn0
    @16
    @35
    nn0uz
    @34
    cc0
    cuz
    1m1e0
    fveq2i
    eqtr4i
    eleq2i
    biimpi
    c1
    @6
    fzsuc2
    sylancr
    adantr
    @21
    @12
    @8
    csuc
    #
    @25
    @20
    @12
    @37
    wceq
    #
    @9
    @20
    @17
    @37
    com
    wcel
    #
    wa
    @37
    cG
    cfv
    #
    @10
    wceq
    @38
    @20
    @39
    @17
    @20
    @30
    @39
    @32
    @8
    peano2
    syl
    @19
    jctil
    @20
    @40
    @8
    cG
    cfv
    #
    c1
    caddc
    co
    #
    @10
    @20
    @30
    @40
    @42
    wceq
    @32
    vx
    @8
    cc0
    cG
    0z
    fzennn.1
    om2uzsuci
    syl
    @20
    @41
    @6
    c1
    caddc
    @20
    @17
    @31
    @41
    @6
    wceq
    @19
    @20
    @31
    cn0
    @16
    @6
    nn0uz
    eleq2i
    biimpi
    com
    @16
    @6
    cG
    f1ocnvfv2
    sylancr
    oveq1d
    eqtrd
    com
    @16
    @37
    @10
    cG
    f1ocnvfv
    sylc
    adantr
    @8
    df-suc
    syl6eq
    3brtr4d
    ex
    nn0ind
end
