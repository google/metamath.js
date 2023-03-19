include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cc0.mm"
include "creps.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cconcat.mm"
include "wceq.mm"
include "repswlen.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "wa.mm"
include "simp1.mm"
include "adantr.mm"
include "simpl2.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "3jca.mm"
include "adantlr.mm"
include "repswsymb.mm"
include "syl.mm"
include "wn.mm"
include "ad2antrr.mm"
include "simpll3.mm"
include "wi.mm"
include "jca.mm"
include "cz.mm"
include "simpr.mm"
include "anim1i.mm"
include "nn0z.mm"
include "anim12i.mm"
include "fzocatel.mm"
include "syl2anc.mm"
include "exp31.mm"
include "3adant1.mm"
include "oveq12.mm"
include "wb.mm"
include "oveq2.mm"
include "notbid.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "imp31.mm"
include "syl3anc.mm"
include "ifeqda.mm"
include "mpteq12dva.mm"
include "cvv.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "ccatfval.mm"
include "mp1i.mm"
include "nn0addcl.mm"
include "reps.mm"
include "3eqtr4d.mm"

theorem repswccat
  let cS: class S
  let cM: class M
  let cN: class N
  let cV: class V
  let vx: setvar x


  assert |- ( ( S e. V /\ N e. NN0 /\ M e. NN0 ) -> ( ( S repeatS N ) ++ ( S repeatS M ) ) = ( S repeatS ( N + M ) ) )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    w3a
    #
    vx
    cc0
    cS
    cN
    creps
    co
    #
    chash
    cfv
    #
    cS
    cM
    creps
    co
    #
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @5
    cfzo
    co
    #
    wcel
    #
    @10
    @4
    cfv
    #
    @10
    @5
    cmin
    co
    #
    @6
    cfv
    #
    cif
    #
    cmpt
    #
    vx
    cc0
    cN
    cM
    caddc
    co
    #
    cfzo
    co
    #
    cS
    cmpt
    #
    @4
    @6
    cconcat
    co
    #
    cS
    @18
    creps
    co
    #
    @3
    vx
    @9
    @16
    @19
    cS
    @3
    @8
    @18
    cc0
    cfzo
    @3
    @5
    cN
    @7
    cM
    caddc
    @0
    @1
    @5
    cN
    wceq
    #
    @2
    cS
    cN
    cV
    repswlen
    3adant3
    #
    @0
    @2
    @7
    cM
    wceq
    #
    @1
    cS
    cM
    cV
    repswlen
    3adant2
    #
    oveq12d
    oveq2d
    @3
    @10
    @9
    wcel
    #
    wa
    #
    @12
    @13
    @15
    cS
    @28
    @12
    wa
    @0
    @1
    @10
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    @13
    cS
    wceq
    @3
    @12
    @31
    @27
    @3
    @12
    wa
    @0
    @1
    @30
    @3
    @0
    @12
    @0
    @1
    @2
    simp1
    #
    adantr
    @0
    @1
    @2
    @12
    simpl2
    @3
    @12
    @30
    @3
    @11
    @29
    @10
    @3
    @5
    cN
    cc0
    cfzo
    @24
    oveq2d
    eleq2d
    biimpa
    3jca
    adantlr
    cS
    @10
    cN
    cV
    repswsymb
    syl
    @28
    @12
    wn
    #
    wa
    @0
    @2
    @14
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @15
    cS
    wceq
    @3
    @0
    @27
    @33
    @32
    ad2antrr
    @0
    @1
    @2
    @27
    @33
    simpll3
    @3
    @27
    @33
    @35
    @23
    @25
    wa
    #
    @3
    @27
    @33
    @35
    wi
    #
    wi
    #
    @3
    @23
    @25
    @24
    @26
    jca
    @3
    @38
    @36
    @10
    @19
    wcel
    #
    @30
    wn
    #
    @10
    cN
    cmin
    co
    #
    @34
    wcel
    #
    wi
    #
    wi
    #
    @1
    @2
    @44
    @0
    @1
    @2
    wa
    #
    @39
    @40
    @42
    @45
    @39
    wa
    #
    @40
    wa
    @39
    @40
    wa
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    @42
    @46
    @39
    @40
    @45
    @39
    simpr
    anim1i
    @45
    @49
    @39
    @40
    @1
    @47
    @2
    @48
    cN
    nn0z
    cM
    nn0z
    anim12i
    ad2antrr
    @10
    cN
    cM
    fzocatel
    syl2anc
    exp31
    3adant1
    @36
    @27
    @39
    @37
    @43
    @36
    @9
    @19
    @10
    @36
    @8
    @18
    cc0
    cfzo
    @5
    cN
    @7
    cM
    caddc
    oveq12
    oveq2d
    eleq2d
    @36
    @33
    @40
    @35
    @42
    @23
    @33
    @40
    wb
    @25
    @23
    @12
    @30
    @23
    @11
    @29
    @10
    @5
    cN
    cc0
    cfzo
    oveq2
    eleq2d
    notbid
    adantr
    @23
    @35
    @42
    wb
    @25
    @23
    @14
    @41
    @34
    @5
    cN
    @10
    cmin
    oveq2
    eleq1d
    adantr
    imbi12d
    imbi12d
    syl5ibr
    mpcom
    imp31
    cS
    @14
    cM
    cV
    repswsymb
    syl3anc
    ifeqda
    mpteq12dva
    @4
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    wa
    @21
    @17
    wceq
    @3
    @50
    @51
    cS
    cN
    creps
    ovex
    cS
    cM
    creps
    ovex
    pm3.2i
    vx
    @4
    @6
    cvv
    cvv
    ccatfval
    mp1i
    @3
    @0
    @18
    cn0
    wcel
    #
    @22
    @20
    wceq
    @32
    @1
    @2
    @52
    @0
    cN
    cM
    nn0addcl
    3adant1
    vx
    cS
    @18
    cV
    reps
    syl2anc
    3eqtr4d
end
