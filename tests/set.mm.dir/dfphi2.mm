include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "cphi.mm"
include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "crab.mm"
include "chash.mm"
include "elnn1uz2.mm"
include "csn.mm"
include "phi1.mm"
include "cz.mm"
include "0z.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "rabid2.mm"
include "elsni.mm"
include "oveq1d.mm"
include "gcd1.mm"
include "syl6eq.mm"
include "mprgbir.mm"
include "fveq2i.mm"
include "3eqtr2i.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fzo01.mm"
include "eqeq1d.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "cfz.mm"
include "eluz2nn.mm"
include "phival.mm"
include "syl.mm"
include "cin.mm"
include "wss.mm"
include "fzossfz.mm"
include "a1i.mm"
include "sseqin2.mm"
include "sylib.mm"
include "fzo0ss1.mm"
include "mpbi.mm"
include "syl6eqr.mm"
include "rabeqdv.mm"
include "inrab2.mm"
include "3eqtr4g.mm"
include "cmin.mm"
include "phibndlem.mm"
include "eluzelz.mm"
include "fzoval.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "cabs.mm"
include "gcd0id.mm"
include "eluzelre.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "eqtrd.mm"
include "eluz2b3.mm"
include "simprbi.mm"
include "eqnetrd.mm"
include "adantr.mm"
include "eleq2s.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "necon2bd.mm"
include "simpr.mm"
include "1z.mm"
include "fzospliti.mm"
include "sylancl.mm"
include "ord.mm"
include "syld.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "3eqtr3d.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem dfphi2
  let vx: setvar x
  let cN: class N

  disjoint N x
  assert |- ( N e. NN -> ( phi ` N ) = ( # ` { x e. ( 0 ..^ N ) | ( x gcd N ) = 1 } ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    wceq
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wo
    cN
    cphi
    cfv
    #
    vx
    cv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    cc0
    cN
    cfzo
    co
    #
    crab
    #
    chash
    cfv
    #
    wceq
    #
    cN
    elnn1uz2
    @1
    @10
    @2
    @1
    c1
    cphi
    cfv
    #
    @4
    c1
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    cc0
    csn
    #
    crab
    #
    chash
    cfv
    #
    @3
    @9
    @11
    c1
    @14
    chash
    cfv
    #
    @16
    phi1
    cc0
    cz
    wcel
    #
    @17
    c1
    wceq
    0z
    cc0
    cz
    hashsng
    ax-mp
    @14
    @15
    chash
    @14
    @15
    wceq
    @13
    vx
    @14
    @13
    vx
    @14
    rabid2
    @4
    @14
    wcel
    #
    @12
    cc0
    c1
    cgcd
    co
    #
    c1
    @19
    @4
    cc0
    c1
    cgcd
    @4
    cc0
    elsni
    #
    oveq1d
    @18
    @20
    c1
    wceq
    0z
    cc0
    gcd1
    ax-mp
    syl6eq
    mprgbir
    fveq2i
    3eqtr2i
    cN
    c1
    cphi
    fveq2
    @1
    @8
    @15
    chash
    @1
    @6
    @13
    vx
    @7
    @14
    @1
    @7
    cc0
    c1
    cfzo
    co
    #
    @14
    cN
    c1
    cc0
    cfzo
    oveq2
    fzo01
    syl6eq
    @1
    @5
    @12
    c1
    cN
    c1
    @4
    cgcd
    oveq2
    eqeq1d
    rabeqbidv
    fveq2d
    3eqtr4a
    @2
    @3
    @6
    vx
    c1
    cN
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    @9
    @2
    @0
    @3
    @25
    wceq
    cN
    eluz2nn
    vx
    cN
    phival
    syl
    @2
    @24
    @8
    chash
    @2
    @24
    c1
    cN
    cfzo
    co
    #
    cin
    #
    @8
    @26
    cin
    #
    @24
    @8
    @2
    @6
    vx
    @23
    @26
    cin
    #
    crab
    @6
    vx
    @7
    @26
    cin
    #
    crab
    @27
    @28
    @2
    @6
    vx
    @29
    @30
    @2
    @29
    @26
    @30
    @2
    @26
    @23
    wss
    #
    @29
    @26
    wceq
    @31
    @2
    c1
    cN
    fzossfz
    a1i
    @26
    @23
    sseqin2
    sylib
    @26
    @7
    wss
    @30
    @26
    wceq
    cN
    fzo0ss1
    @26
    @7
    sseqin2
    mpbi
    syl6eqr
    rabeqdv
    @6
    vx
    @23
    @26
    inrab2
    @6
    vx
    @7
    @26
    inrab2
    3eqtr4g
    @2
    @24
    @26
    wss
    @27
    @24
    wceq
    @2
    @24
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @26
    vx
    cN
    phibndlem
    @2
    cN
    cz
    wcel
    #
    @26
    @32
    wceq
    c2
    cN
    eluzelz
    #
    c1
    cN
    fzoval
    syl
    sseqtr4d
    @24
    @26
    df-ss
    sylib
    @2
    @8
    @26
    wss
    #
    @28
    @8
    wceq
    @2
    @6
    @4
    @26
    wcel
    #
    wi
    #
    vx
    @7
    wral
    @35
    @2
    @37
    vx
    @7
    @2
    @4
    @7
    wcel
    #
    wa
    #
    @6
    @4
    @22
    wcel
    #
    wn
    @36
    @39
    @40
    @5
    c1
    @39
    @5
    c1
    wne
    @40
    cc0
    cN
    cgcd
    co
    #
    c1
    wne
    #
    @2
    @42
    @38
    @2
    @41
    cN
    c1
    @2
    @41
    cN
    cabs
    cfv
    #
    cN
    @2
    @33
    @41
    @43
    wceq
    @34
    cN
    gcd0id
    syl
    @2
    cN
    c2
    cN
    eluzelre
    @2
    cN
    cN
    eluzge2nn0
    nn0ge0d
    absidd
    eqtrd
    @2
    @0
    cN
    c1
    wne
    cN
    eluz2b3
    simprbi
    eqnetrd
    adantr
    @40
    @5
    @41
    c1
    @5
    @41
    wceq
    @4
    @14
    @22
    @19
    @4
    cc0
    cN
    cgcd
    @21
    oveq1d
    fzo01
    eleq2s
    neeq1d
    syl5ibrcom
    necon2bd
    @39
    @40
    @36
    @39
    @38
    c1
    cz
    wcel
    @40
    @36
    wo
    @2
    @38
    simpr
    1z
    @4
    cc0
    cN
    c1
    fzospliti
    sylancl
    ord
    syld
    ralrimiva
    @6
    vx
    @7
    @26
    rabss
    sylibr
    @8
    @26
    df-ss
    sylib
    3eqtr3d
    fveq2d
    eqtrd
    jaoi
    sylbi
end
