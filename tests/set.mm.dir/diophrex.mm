include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cdioph.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvabv.mm"
include "cc0.mm"
include "wa.mm"
include "cn.mm"
include "cmap.mm"
include "cmzp.mm"
include "rexeq.mm"
include "abbidv.mm"
include "adantl.mm"
include "wex.mm"
include "anbi1d.mm"
include "rexab.mm"
include "r19.41v.mm"
include "exbii.mm"
include "rexcom4.mm"
include "anass.mm"
include "vex.mm"
include "resex.mm"
include "anbi2d.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "ancom.mm"
include "wss.mm"
include "simpl2.mm"
include "fzss2.mm"
include "resabs1.mm"
include "3syl.mm"
include "syl5bb.mm"
include "syl5bbr.mm"
include "eldioph3.mm"
include "3ad2antl1.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "eldioph3b.mm"
include "simprbi.mm"
include "3ad2ant3.mm"
include "r19.29a.mm"
include "syl5eqelr.mm"

theorem diophrex
  let vu: setvar u
  let vt: setvar t
  let cS: class S
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e

  disjoint N t
  disjoint N u
  disjoint t u
  disjoint S t
  disjoint S u
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint a t
  disjoint b t
  disjoint c t
  disjoint d t
  disjoint e t
  disjoint a u
  disjoint b u
  disjoint c u
  disjoint d u
  disjoint e u
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M d
  disjoint M e
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  assert |- ( ( N e. NN0 /\ M e. ( ZZ>= ` N ) /\ S e. ( Dioph ` M ) ) -> { t | E. u e. S t = ( u |` ( 1 ... N ) ) } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cM
    cN
    cuz
    cfv
    wcel
    #
    cS
    cM
    cdioph
    cfv
    wcel
    #
    w3a
    #
    vt
    cv
    #
    vu
    cv
    #
    c1
    cN
    cfz
    co
    #
    cres
    #
    wceq
    #
    vu
    cS
    wrex
    #
    vt
    cab
    va
    cv
    #
    vb
    cv
    #
    @6
    cres
    #
    wceq
    #
    vb
    cS
    wrex
    #
    va
    cab
    #
    cN
    cdioph
    cfv
    #
    @14
    @9
    va
    vt
    @10
    @4
    wceq
    #
    @14
    @4
    @12
    wceq
    #
    vb
    cS
    wrex
    @9
    @17
    @13
    @18
    vb
    cS
    @10
    @4
    @12
    eqeq1
    rexbidv
    @18
    @8
    vb
    vu
    cS
    @11
    @5
    wceq
    @12
    @7
    @4
    @11
    @5
    @6
    reseq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvabv
    @3
    cS
    vd
    cv
    #
    ve
    cv
    #
    c1
    cM
    cfz
    co
    #
    cres
    #
    wceq
    #
    @20
    vc
    cv
    #
    cfv
    cc0
    wceq
    #
    wa
    #
    ve
    cn0
    cn
    cmap
    co
    #
    wrex
    #
    vd
    cab
    #
    wceq
    #
    @15
    @16
    wcel
    vc
    cn
    cmzp
    cfv
    #
    @3
    @24
    @31
    wcel
    #
    wa
    #
    @30
    wa
    @15
    @13
    vb
    @29
    wrex
    #
    va
    cab
    #
    @16
    @30
    @15
    @35
    wceq
    @33
    @30
    @14
    @34
    va
    @13
    vb
    cS
    @29
    rexeq
    abbidv
    adantl
    @33
    @35
    @16
    wcel
    @30
    @33
    @35
    @10
    @20
    @6
    cres
    #
    wceq
    #
    @25
    wa
    #
    ve
    @27
    wrex
    #
    va
    cab
    #
    @16
    @33
    @34
    @39
    va
    @34
    @11
    @22
    wceq
    #
    @25
    wa
    #
    ve
    @27
    wrex
    #
    @13
    wa
    #
    vb
    wex
    #
    @33
    @39
    @28
    @43
    @13
    vb
    vd
    @19
    @11
    wceq
    #
    @26
    @42
    ve
    @27
    @46
    @23
    @41
    @25
    @19
    @11
    @22
    eqeq1
    anbi1d
    rexbidv
    rexab
    @45
    @42
    @13
    wa
    #
    ve
    @27
    wrex
    #
    vb
    wex
    #
    @33
    @39
    @48
    @44
    vb
    @42
    @13
    ve
    @27
    r19.41v
    exbii
    @49
    @47
    vb
    wex
    #
    ve
    @27
    wrex
    @33
    @39
    @47
    ve
    vb
    @27
    rexcom4
    @33
    @50
    @38
    ve
    @27
    @50
    @25
    @10
    @22
    @6
    cres
    #
    wceq
    #
    wa
    #
    @33
    @38
    @50
    @41
    @25
    @13
    wa
    #
    wa
    #
    vb
    wex
    @53
    @47
    @55
    vb
    @41
    @25
    @13
    anass
    exbii
    @54
    @53
    vb
    @22
    @20
    @21
    ve
    vex
    resex
    @41
    @13
    @52
    @25
    @41
    @12
    @51
    @10
    @11
    @22
    @6
    reseq1
    eqeq2d
    anbi2d
    ceqsexv
    bitri
    @53
    @52
    @25
    wa
    @33
    @38
    @25
    @52
    ancom
    @33
    @52
    @37
    @25
    @33
    @51
    @36
    @10
    @33
    @1
    @6
    @21
    wss
    @51
    @36
    wceq
    @0
    @1
    @2
    @32
    simpl2
    cN
    c1
    cM
    fzss2
    @20
    @6
    @21
    resabs1
    3syl
    eqeq2d
    anbi1d
    syl5bb
    syl5bb
    rexbidv
    syl5bbr
    syl5bbr
    syl5bb
    abbidv
    @0
    @1
    @32
    @40
    @16
    wcel
    @2
    ve
    va
    @24
    cN
    eldioph3
    3ad2antl1
    eqeltrd
    adantr
    eqeltrd
    @2
    @0
    @30
    vc
    @31
    wrex
    #
    @1
    @2
    cM
    cn0
    wcel
    @56
    ve
    vd
    cS
    cM
    vc
    eldioph3b
    simprbi
    3ad2ant3
    r19.29a
    syl5eqelr
end
