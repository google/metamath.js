include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cpfx.mm"
include "c1.mm"
include "cs2.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "2nn0.mm"
include "a1i.mm"
include "lencl.mm"
include "adantr.mm"
include "simpr.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "pfxlen.mm"
include "cpr.mm"
include "s2len.mm"
include "eqcomi.mm"
include "w3a.mm"
include "simpl.mm"
include "cn.mm"
include "2nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "3jca.mm"
include "pfxfv.mm"
include "syl.mm"
include "cvv.mm"
include "fvex.mm"
include "s2fv0.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "clt.mm"
include "1nn0.mm"
include "1lt2.mm"
include "elfzo0.mm"
include "mpbir3an.mm"
include "mp3an3.mm"
include "s2fv1.mm"
include "wb.mm"
include "0nn0.mm"
include "pm3.2i.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "ralprg.mm"
include "mpbir2and.mm"
include "eqeq1.mm"
include "oveq2.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "adantl.mm"
include "mpdan.mm"
include "pfxcl.mm"
include "simp2.mm"
include "cr.mm"
include "wi.mm"
include "1red.mm"
include "2re.mm"
include "nn0re.mm"
include "ltleletr.mm"
include "mpani.mm"
include "imp.mm"
include "3adant1.mm"
include "jca.mm"
include "elnnnn0c.mm"
include "sylibr.mm"
include "sylbi.mm"
include "wrdsymbcl.mm"
include "sylan2.mm"
include "ltletr.mm"
include "3impia.mm"
include "s2cld.mm"
include "eqwrd.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "syldan.mm"

theorem pfx2
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ 2 <_ ( # ` W ) ) -> ( W prefix 2 ) = <" ( W ` 0 ) ( W ` 1 ) "> )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    c2
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    c2
    cc0
    @2
    cfz
    co
    wcel
    #
    cW
    c2
    cpfx
    co
    #
    cc0
    cW
    cfv
    #
    c1
    cW
    cfv
    #
    cs2
    #
    wceq
    #
    @1
    @3
    wa
    #
    c2
    cn0
    wcel
    #
    @2
    cn0
    wcel
    #
    @3
    @4
    @11
    @10
    2nn0
    a1i
    @1
    @12
    @3
    cV
    cW
    lencl
    adantr
    @1
    @3
    simpr
    c2
    @2
    elfz2nn0
    #
    syl3anbrc
    @1
    @4
    wa
    #
    @9
    @5
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    wceq
    #
    vi
    cv
    #
    @5
    cfv
    #
    @18
    @8
    cfv
    #
    wceq
    #
    vi
    cc0
    @15
    cfzo
    co
    #
    wral
    #
    wa
    #
    @14
    @15
    c2
    wceq
    #
    @24
    cV
    cW
    c2
    pfxlen
    @14
    @25
    wa
    #
    @24
    c2
    @16
    wceq
    #
    @21
    vi
    cc0
    c1
    cpr
    #
    wral
    #
    @27
    @26
    @16
    c2
    @6
    @7
    s2len
    eqcomi
    a1i
    @26
    @29
    cc0
    @5
    cfv
    #
    cc0
    @8
    cfv
    #
    wceq
    #
    c1
    @5
    cfv
    #
    c1
    @8
    cfv
    #
    wceq
    #
    @26
    @30
    @6
    @31
    @26
    @1
    @4
    cc0
    cc0
    c2
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    @30
    @6
    wceq
    @14
    @38
    @25
    @14
    @1
    @4
    @37
    @1
    @4
    simpl
    @1
    @4
    simpr
    @37
    @14
    @37
    c2
    cn
    wcel
    #
    2nn
    c2
    lbfzo0
    mpbir
    a1i
    3jca
    adantr
    cc0
    c2
    cV
    cW
    pfxfv
    syl
    @6
    cvv
    wcel
    @31
    @6
    wceq
    cc0
    cW
    fvex
    @6
    @7
    cvv
    s2fv0
    ax-mp
    syl6eqr
    @14
    @35
    @25
    @14
    @33
    @7
    @34
    @1
    @4
    c1
    @36
    wcel
    #
    @33
    @7
    wceq
    @40
    c1
    cn0
    wcel
    #
    @39
    c1
    c2
    clt
    wbr
    #
    1nn0
    2nn
    1lt2
    c1
    c2
    elfzo0
    mpbir3an
    c1
    c2
    cV
    cW
    pfxfv
    mp3an3
    @7
    cvv
    wcel
    @34
    @7
    wceq
    c1
    cW
    fvex
    @6
    @7
    cvv
    s2fv1
    ax-mp
    syl6eqr
    adantr
    @26
    cc0
    cn0
    wcel
    #
    @41
    wa
    #
    @29
    @32
    @35
    wa
    wb
    @44
    @26
    @43
    @41
    0nn0
    1nn0
    pm3.2i
    a1i
    @21
    @32
    @35
    vi
    cc0
    c1
    cn0
    cn0
    @18
    cc0
    wceq
    @19
    @30
    @20
    @31
    @18
    cc0
    @5
    fveq2
    @18
    cc0
    @8
    fveq2
    eqeq12d
    @18
    c1
    wceq
    @19
    @33
    @20
    @34
    @18
    c1
    @5
    fveq2
    @18
    c1
    @8
    fveq2
    eqeq12d
    ralprg
    syl
    mpbir2and
    @25
    @24
    @27
    @29
    wa
    wb
    @14
    @25
    @17
    @27
    @23
    @29
    @15
    c2
    @16
    eqeq1
    @25
    @21
    vi
    @22
    @28
    @25
    @22
    @36
    @28
    @15
    c2
    cc0
    cfzo
    oveq2
    fzo0to2pr
    syl6eq
    raleqdv
    anbi12d
    adantl
    mpbir2and
    mpdan
    @14
    @5
    @0
    wcel
    #
    @8
    @0
    wcel
    @9
    @24
    wb
    @1
    @45
    @4
    cV
    cW
    c2
    pfxcl
    adantr
    @14
    @6
    @7
    cV
    @4
    @1
    cc0
    cc0
    @2
    cfzo
    co
    #
    wcel
    #
    @6
    cV
    wcel
    @4
    @2
    cn
    wcel
    #
    @47
    @4
    @11
    @12
    @3
    w3a
    #
    @48
    @13
    @49
    @12
    c1
    @2
    cle
    wbr
    #
    wa
    @48
    @49
    @12
    @50
    @11
    @12
    @3
    simp2
    @12
    @3
    @50
    @11
    @12
    @3
    @50
    @12
    @42
    @3
    @50
    1lt2
    @12
    c1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    w3a
    #
    @42
    @3
    wa
    #
    @50
    wi
    @12
    @51
    @52
    @53
    @12
    1red
    @52
    @12
    2re
    a1i
    @2
    nn0re
    3jca
    #
    c1
    c2
    @2
    ltleletr
    syl
    mpani
    imp
    3adant1
    jca
    @2
    elnnnn0c
    sylibr
    sylbi
    #
    @2
    lbfzo0
    sylibr
    cc0
    cV
    cW
    wrdsymbcl
    sylan2
    @4
    @1
    c1
    @46
    wcel
    #
    @7
    cV
    wcel
    @4
    @41
    @48
    c1
    @2
    clt
    wbr
    #
    @58
    @41
    @4
    1nn0
    a1i
    @57
    @4
    @49
    @59
    @13
    @11
    @12
    @3
    @59
    @11
    @12
    wa
    #
    @42
    @3
    @59
    1lt2
    @60
    @54
    @55
    @59
    wi
    @12
    @54
    @11
    @56
    adantl
    c1
    c2
    @2
    ltletr
    syl
    mpani
    3impia
    sylbi
    c1
    @2
    elfzo0
    syl3anbrc
    c1
    cV
    cW
    wrdsymbcl
    sylan2
    s2cld
    @5
    vi
    cV
    @8
    eqwrd
    syl2anc
    mpbird
    syldan
end
