include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "w3a.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "ccom.mm"
include "wss.mm"
include "wex.mm"
include "caddc.mm"
include "cvv.mm"
include "ovexd.mm"
include "simprlr.mm"
include "simpll2.mm"
include "eleqtrd.mm"
include "simpll3.mm"
include "simprll.mm"
include "eluznn0.mm"
include "syl2anc.mm"
include "uzaddcl.mm"
include "simplr.mm"
include "3eltr4d.mm"
include "vex.mm"
include "brcogw.mm"
include "ex.mm"
include "mp3an.mm"
include "simprr.mm"
include "simprl.mm"
include "simpll1.mm"
include "relexpaddss.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "sseqtr4d.mm"
include "ssbrd.mm"
include "syl5.mm"
include "impr.mm"
include "jca.mm"
include "spcimedv.mm"
include "exlimdvv.mm"
include "reeanv.mm"
include "r2ex.mm"
include "bitr3i.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "alrimiv.mm"
include "cotr.mm"
include "briunov2uz.mm"
include "weq.mm"
include "oveq2.mm"
include "breqd.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "albidv.mm"
include "syl5bb.mm"
include "biimprd.mm"
include "3adant3.mm"
include "mpd.mm"

theorem iunrelexpuztr
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  assume mptiunrelexp.def: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )

  disjoint M n
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint n r
  disjoint C n
  disjoint N n
  disjoint C r
  disjoint N r
  disjoint C N
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint i j
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N i
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint R i
  disjoint R j
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint V i
  disjoint V j
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( R e. V /\ N = ( ZZ>= ` M ) /\ M e. NN0 ) -> ( ( C ` R ) o. ( C ` R ) ) C_ ( C ` R ) )

  proof
    cR
    cV
    wcel
    #
    cN
    cM
    cuz
    cfv
    #
    wceq
    #
    cM
    cn0
    wcel
    #
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    vi
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vi
    cN
    wrex
    #
    @6
    vz
    cv
    #
    cR
    vj
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vj
    cN
    wrex
    #
    wa
    #
    @5
    @11
    cR
    vn
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vn
    cN
    wrex
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    cR
    cC
    cfv
    #
    @25
    ccom
    @25
    wss
    #
    @4
    @23
    vx
    @4
    @22
    vy
    @4
    @21
    vz
    @4
    @7
    cN
    wcel
    #
    @12
    cN
    wcel
    #
    wa
    #
    @9
    @14
    wa
    #
    wa
    #
    vj
    wex
    vi
    wex
    #
    @17
    cN
    wcel
    #
    @19
    wa
    #
    vn
    wex
    #
    @16
    @20
    @4
    @31
    @35
    vi
    vj
    @4
    @34
    @31
    vn
    @12
    @7
    caddc
    co
    #
    cvv
    @4
    @12
    @7
    caddc
    ovexd
    @4
    @17
    @36
    wceq
    #
    wa
    #
    @31
    @34
    @38
    @31
    wa
    #
    @33
    @19
    @39
    @36
    @1
    @17
    cN
    @39
    @12
    @1
    wcel
    #
    @7
    cn0
    wcel
    #
    @36
    @1
    wcel
    @39
    @12
    cN
    @1
    @38
    @27
    @28
    @30
    simprlr
    @0
    @2
    @3
    @37
    @31
    simpll2
    #
    eleqtrd
    @39
    @3
    @7
    @1
    wcel
    #
    @41
    @0
    @2
    @3
    @37
    @31
    simpll3
    @39
    @7
    cN
    @1
    @38
    @27
    @28
    @30
    simprll
    @42
    eleqtrd
    @7
    cM
    eluznn0
    #
    syl2anc
    @7
    cM
    @12
    uzaddcl
    syl2anc
    @4
    @37
    @31
    simplr
    @42
    3eltr4d
    @38
    @29
    @30
    @19
    @30
    @5
    @11
    @13
    @8
    ccom
    #
    wbr
    #
    @38
    @29
    wa
    #
    @19
    @5
    cvv
    wcel
    #
    @11
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    @30
    @46
    wi
    vx
    vex
    vz
    vex
    vy
    vex
    @48
    @49
    @50
    w3a
    @30
    @46
    @5
    @11
    @13
    @8
    cvv
    cvv
    @6
    cvv
    brcogw
    ex
    mp3an
    @47
    @45
    @18
    @5
    @11
    @47
    @45
    cR
    @36
    crelexp
    co
    #
    @18
    @47
    @12
    cn0
    wcel
    #
    @41
    @0
    @45
    @51
    wss
    @47
    @3
    @40
    @52
    @0
    @2
    @3
    @37
    @29
    simpll3
    #
    @47
    @12
    cN
    @1
    @38
    @27
    @28
    simprr
    @0
    @2
    @3
    @37
    @29
    simpll2
    #
    eleqtrd
    @12
    cM
    eluznn0
    syl2anc
    @47
    @3
    @43
    @41
    @53
    @47
    @7
    cN
    @1
    @38
    @27
    @28
    simprl
    @54
    eleqtrd
    @44
    syl2anc
    @0
    @2
    @3
    @37
    @29
    simpll1
    cR
    @7
    @12
    cV
    relexpaddss
    syl3anc
    @47
    @17
    @36
    cR
    crelexp
    @4
    @37
    @29
    simplr
    oveq2d
    sseqtr4d
    ssbrd
    syl5
    impr
    jca
    ex
    spcimedv
    exlimdvv
    @16
    @30
    vj
    cN
    wrex
    vi
    cN
    wrex
    @32
    @9
    @14
    vi
    vj
    cN
    cN
    reeanv
    @30
    vi
    vj
    cN
    cN
    r2ex
    bitr3i
    @19
    vn
    cN
    df-rex
    3imtr4g
    alrimiv
    alrimiv
    alrimiv
    @0
    @2
    @24
    @26
    wi
    @3
    @0
    @2
    wa
    #
    @26
    @24
    @26
    @5
    @6
    @25
    wbr
    #
    @6
    @11
    @25
    wbr
    #
    wa
    #
    @5
    @11
    @25
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    @55
    @24
    vx
    vy
    vz
    @25
    cotr
    @55
    @62
    @23
    vx
    @55
    @61
    @22
    vy
    @55
    @60
    @21
    vz
    @55
    @58
    @16
    @59
    @20
    @55
    @56
    @10
    @57
    @15
    @55
    @56
    @5
    @6
    @18
    wbr
    #
    vn
    cN
    wrex
    @10
    cC
    cR
    cV
    vn
    crelexp
    cM
    cN
    @5
    @6
    vr
    mptiunrelexp.def
    briunov2uz
    @63
    @9
    vn
    vi
    cN
    vn
    vi
    weq
    @18
    @8
    @5
    @6
    @17
    @7
    cR
    crelexp
    oveq2
    breqd
    cbvrexv
    syl6bb
    @55
    @57
    @6
    @11
    @18
    wbr
    #
    vn
    cN
    wrex
    @15
    cC
    cR
    cV
    vn
    crelexp
    cM
    cN
    @6
    @11
    vr
    mptiunrelexp.def
    briunov2uz
    @64
    @14
    vn
    vj
    cN
    vn
    vj
    weq
    @18
    @13
    @6
    @11
    @17
    @12
    cR
    crelexp
    oveq2
    breqd
    cbvrexv
    syl6bb
    anbi12d
    cC
    cR
    cV
    vn
    crelexp
    cM
    cN
    @5
    @11
    vr
    mptiunrelexp.def
    briunov2uz
    imbi12d
    albidv
    albidv
    albidv
    syl5bb
    biimprd
    3adant3
    mpd
end
