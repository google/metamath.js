include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "w3a.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "wn.mm"
include "wnel.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "wne.mm"
include "wi.mm"
include "3ad2ant1.mm"
include "ralcom.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo1.mm"
include "nnne0.mm"
include "necomd.mm"
include "sylbi.mm"
include "adantl.mm"
include "neeq1.mm"
include "syl5ibr.mm"
include "expd.mm"
include "cle.mm"
include "cr.mm"
include "nnre.mm"
include "adantr.mm"
include "ltlend.mm"
include "simpr.mm"
include "syl6bi.mm"
include "3impia.mm"
include "jaoi.mm"
include "impcom.mm"
include "3adant1.mm"
include "imp.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "eleq1.mm"
include "cmin.mm"
include "fzo0end.mm"
include "syl5eqel.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "nesym.mm"
include "syl6ib.mm"
include "ralimdva.mm"
include "syl5bi.mm"
include "mpd.mm"
include "ralnex.mm"
include "sylib.mm"
include "wfun.mm"
include "cvv.mm"
include "cword.mm"
include "wf.mm"
include "wrdf.mm"
include "ffun.mm"
include "3syl.mm"
include "fvelima.mm"
include "ex.mm"
include "mtod.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem pthdlem2lem
  let wph: wff ph
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  assume pthd.p: |- ( ph -> P e. Word _V )
  assume pthd.r: |- R = ( ( # ` P ) - 1 )
  assume pthd.s: |- ( ph -> A. i e. ( 0 ..^ ( # ` P ) ) A. j e. ( 1 ..^ R ) ( i =/= j -> ( P ` i ) =/= ( P ` j ) ) )

  disjoint P i
  disjoint P j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint i ph
  disjoint j ph
  disjoint I i
  disjoint I j
  assert |- ( ( ph /\ ( # ` P ) e. NN /\ ( I = 0 \/ I = R ) ) -> ( P ` I ) e/ ( P " ( 1 ..^ R ) ) )

  proof
    wph
    cP
    chash
    cfv
    #
    cn
    wcel
    #
    cI
    cc0
    wceq
    #
    cI
    cR
    wceq
    #
    wo
    #
    w3a
    #
    cI
    cP
    cfv
    #
    cP
    c1
    cR
    cfzo
    co
    #
    cima
    #
    wcel
    #
    wn
    @6
    @8
    wnel
    @5
    @9
    vj
    cv
    #
    cP
    cfv
    #
    @6
    wceq
    #
    vj
    @7
    wrex
    #
    @5
    @12
    wn
    #
    vj
    @7
    wral
    #
    @13
    wn
    @5
    vi
    cv
    #
    @10
    wne
    #
    @16
    cP
    cfv
    #
    @11
    wne
    #
    wi
    #
    vj
    @7
    wral
    vi
    cc0
    @0
    cfzo
    co
    #
    wral
    #
    @15
    wph
    @1
    @22
    @4
    pthd.s
    3ad2ant1
    @22
    @20
    vi
    @21
    wral
    #
    vj
    @7
    wral
    @5
    @15
    @20
    vi
    vj
    @21
    @7
    ralcom
    @5
    @23
    @14
    vj
    @7
    @5
    @10
    @7
    wcel
    #
    wa
    #
    @23
    @6
    @11
    wne
    #
    @14
    @25
    @23
    cI
    @10
    wne
    #
    @26
    @5
    @24
    @27
    @1
    @4
    @24
    @27
    wi
    #
    wph
    @4
    @1
    @28
    @2
    @1
    @28
    wi
    @3
    @2
    @1
    @24
    @27
    @1
    @24
    wa
    #
    @27
    @2
    cc0
    @10
    wne
    #
    @24
    @30
    @1
    @24
    @10
    cn
    wcel
    #
    cR
    cn
    wcel
    #
    @10
    cR
    clt
    wbr
    #
    w3a
    #
    @30
    cR
    @10
    elfzo1
    #
    @31
    @32
    @30
    @33
    @31
    @10
    cc0
    @10
    nnne0
    necomd
    3ad2ant1
    sylbi
    adantl
    cI
    cc0
    @10
    neeq1
    syl5ibr
    expd
    @3
    @1
    @24
    @27
    @29
    @27
    @3
    cR
    @10
    wne
    #
    @24
    @36
    @1
    @24
    @34
    @36
    @35
    @31
    @32
    @33
    @36
    @31
    @32
    wa
    #
    @33
    @10
    cR
    cle
    wbr
    #
    @36
    wa
    @36
    @37
    @10
    cR
    @31
    @10
    cr
    wcel
    @32
    @10
    nnre
    adantr
    @32
    cR
    cr
    wcel
    @31
    cR
    nnre
    adantl
    ltlend
    @38
    @36
    simpr
    syl6bi
    3impia
    sylbi
    adantl
    cI
    cR
    @10
    neeq1
    syl5ibr
    expd
    jaoi
    impcom
    3adant1
    imp
    @25
    cI
    @21
    wcel
    #
    @23
    @27
    @26
    wi
    #
    wi
    @5
    @39
    @24
    @1
    @4
    @39
    wph
    @4
    @1
    @39
    @2
    @1
    @39
    wi
    @3
    @1
    @39
    @2
    cc0
    @21
    wcel
    #
    @41
    @1
    @0
    lbfzo0
    biimpri
    cI
    cc0
    @21
    eleq1
    syl5ibr
    @1
    @39
    @3
    cR
    @21
    wcel
    @1
    cR
    @0
    c1
    cmin
    co
    @21
    pthd.r
    @0
    fzo0end
    syl5eqel
    cI
    cR
    @21
    eleq1
    syl5ibr
    jaoi
    impcom
    3adant1
    adantr
    @20
    @40
    vi
    cI
    @21
    @16
    cI
    wceq
    #
    @17
    @27
    @19
    @26
    @16
    cI
    @10
    neeq1
    @42
    @18
    @6
    @11
    @16
    cI
    cP
    fveq2
    neeq1d
    imbi12d
    rspcv
    syl
    mpid
    @6
    @11
    nesym
    syl6ib
    ralimdva
    syl5bi
    mpd
    @12
    vj
    @7
    ralnex
    sylib
    @5
    cP
    wfun
    #
    @9
    @13
    wi
    wph
    @1
    @43
    @4
    wph
    cP
    cvv
    cword
    wcel
    @21
    cvv
    cP
    wf
    @43
    pthd.p
    cvv
    cP
    wrdf
    @21
    cvv
    cP
    ffun
    3syl
    3ad2ant1
    @43
    @9
    @13
    vj
    @6
    @7
    cP
    fvelima
    ex
    syl
    mtod
    @6
    @8
    df-nel
    sylibr
end
