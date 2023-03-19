include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csupp.mm"
include "co.mm"
include "wral.mm"
include "wo.mm"
include "cn0.mm"
include "cmap.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "wi.mm"
include "0nn0.mm"
include "a1i.mm"
include "wb.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "ral0.mm"
include "raleq.mm"
include "mpbii.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "ralimi.mm"
include "jaoi.mm"
include "rspcedvd.mm"
include "2a1d.mm"
include "wn.mm"
include "wa.mm"
include "ciun.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wne.mm"
include "simplr.mm"
include "simpr.mm"
include "ioran.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cbvralv.mm"
include "notbii.mm"
include "anbi2i.mm"
include "bitri.mm"
include "rexnal.mm"
include "df-ne.mm"
include "bicomi.mm"
include "rexbii.mm"
include "sylbb1.mm"
include "sylbi.mm"
include "ad2antrr.mm"
include "iunn0.mm"
include "sylib.mm"
include "jca.mm"
include "cbviunv.mm"
include "eqid.mm"
include "fsuppmapnn0fiublem.mm"
include "sylc.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfor.mm"
include "nfn.mm"
include "nfan.mm"
include "ralbid.mm"
include "neeq1i.mm"
include "fsuppmapnn0fiub.mm"
include "exp31.mm"
include "pm2.61i.mm"

theorem fsuppmapnn0fiubex
  let cR: class R
  let vf: setvar f
  let vm: setvar m
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vg: setvar g

  disjoint M f
  disjoint M m
  disjoint f m
  disjoint R f
  disjoint R m
  disjoint V f
  disjoint V m
  disjoint Z f
  disjoint Z m
  disjoint M g
  disjoint f g
  disjoint g m
  disjoint Z g
  assert |- ( ( M C_ ( R ^m NN0 ) /\ M e. Fin /\ Z e. V ) -> ( A. f e. M f finSupp Z -> E. m e. NN0 A. f e. M ( f supp Z ) C_ ( 0 ... m ) ) )

  proof
    c0
    cM
    wceq
    #
    vf
    cv
    #
    cZ
    csupp
    co
    #
    c0
    wceq
    #
    vf
    cM
    wral
    #
    wo
    #
    cM
    cR
    cn0
    cmap
    co
    wss
    cM
    cfn
    wcel
    cZ
    cV
    wcel
    w3a
    #
    @1
    cZ
    cfsupp
    wbr
    #
    vf
    cM
    wral
    #
    @2
    cc0
    vm
    cv
    #
    cfz
    co
    #
    wss
    #
    vf
    cM
    wral
    #
    vm
    cn0
    wrex
    #
    wi
    wi
    @5
    @13
    @6
    @8
    @5
    @12
    @2
    cc0
    cc0
    cfz
    co
    #
    wss
    #
    vf
    cM
    wral
    #
    vm
    cc0
    cn0
    cc0
    cn0
    wcel
    @5
    0nn0
    a1i
    @9
    cc0
    wceq
    #
    @12
    @16
    wb
    @5
    @17
    @11
    @15
    vf
    cM
    @17
    @10
    @14
    @2
    @9
    cc0
    cc0
    cfz
    oveq2
    sseq2d
    ralbidv
    adantl
    @0
    @16
    @4
    @0
    @15
    vf
    c0
    wral
    @16
    @15
    vf
    ral0
    @15
    vf
    c0
    cM
    raleq
    mpbii
    @3
    @15
    vf
    cM
    @3
    @15
    c0
    @14
    wss
    @14
    0ss
    @2
    c0
    @14
    sseq1
    mpbiri
    ralimi
    jaoi
    rspcedvd
    2a1d
    @5
    wn
    #
    @6
    @8
    @13
    @18
    @6
    wa
    #
    @8
    wa
    #
    @12
    @2
    cc0
    vg
    cM
    vg
    cv
    #
    cZ
    csupp
    co
    #
    ciun
    #
    cr
    clt
    csup
    #
    cfz
    co
    #
    wss
    #
    vf
    cM
    wral
    #
    vm
    @24
    cn0
    @20
    @6
    @8
    @23
    c0
    wne
    #
    wa
    #
    @24
    cn0
    wcel
    @18
    @6
    @8
    simplr
    #
    @20
    @8
    @28
    @19
    @8
    simpr
    #
    @20
    @22
    c0
    wne
    #
    vg
    cM
    wrex
    #
    @28
    @18
    @33
    @6
    @8
    @18
    @0
    wn
    #
    @22
    c0
    wceq
    #
    vg
    cM
    wral
    #
    wn
    #
    wa
    #
    @33
    @18
    @34
    @4
    wn
    #
    wa
    #
    @38
    @0
    @4
    ioran
    #
    @39
    @37
    @34
    @4
    @36
    @3
    @35
    vf
    vg
    cM
    @1
    @21
    wceq
    @2
    @22
    c0
    @1
    @21
    cZ
    csupp
    oveq1
    #
    eqeq1d
    cbvralv
    notbii
    anbi2i
    bitri
    @37
    @33
    @34
    @35
    wn
    #
    vg
    cM
    wrex
    @37
    @33
    @35
    vg
    cM
    rexnal
    @43
    @32
    vg
    cM
    @32
    @43
    @22
    c0
    df-ne
    bicomi
    rexbii
    sylbb1
    adantl
    sylbi
    ad2antrr
    vg
    cM
    @22
    iunn0
    sylib
    jca
    cR
    @24
    @23
    vf
    cM
    cV
    cZ
    vg
    vf
    cM
    @22
    @2
    @21
    @1
    cZ
    csupp
    oveq1
    cbviunv
    #
    @24
    eqid
    #
    fsuppmapnn0fiublem
    sylc
    @20
    @9
    @24
    wceq
    #
    wa
    @11
    @26
    vf
    cM
    @20
    @46
    vf
    @19
    @8
    vf
    @18
    @6
    vf
    @5
    vf
    @0
    @4
    vf
    @0
    vf
    nfv
    @3
    vf
    cM
    nfra1
    nfor
    nfn
    @6
    vf
    nfv
    nfan
    @7
    vf
    cM
    nfra1
    nfan
    @46
    vf
    nfv
    nfan
    @46
    @11
    @26
    wb
    @20
    @46
    @10
    @25
    @2
    @9
    @24
    cc0
    cfz
    oveq2
    sseq2d
    adantl
    ralbid
    @20
    @6
    @29
    @27
    @30
    @20
    @8
    @28
    @31
    @20
    @2
    c0
    wne
    #
    vf
    cM
    wrex
    #
    @28
    @18
    @48
    @6
    @8
    @18
    @40
    @48
    @41
    @39
    @48
    @34
    @3
    wn
    #
    vf
    cM
    wrex
    @39
    @48
    @3
    vf
    cM
    rexnal
    @49
    @47
    vf
    cM
    @47
    @49
    @2
    c0
    df-ne
    bicomi
    rexbii
    sylbb1
    adantl
    sylbi
    ad2antrr
    @48
    vf
    cM
    @2
    ciun
    #
    c0
    wne
    @28
    vf
    cM
    @2
    iunn0
    @50
    @23
    c0
    vf
    vg
    cM
    @2
    @22
    @42
    cbviunv
    neeq1i
    bitri
    sylib
    jca
    cR
    @24
    @23
    vf
    cM
    cV
    cZ
    @44
    @45
    fsuppmapnn0fiub
    sylc
    rspcedvd
    exp31
    pm2.61i
end
