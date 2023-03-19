include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cofc.mm"
include "wcel.mm"
include "wf.mm"
include "cword.mm"
include "fconst6g.mm"
include "iswrdi.mm"
include "3syl.mm"
include "cmul.mm"
include "cfn.mm"
include "wceq.mm"
include "fzofi.mm"
include "snfi.mm"
include "hashxp.mm"
include "mp2an.mm"
include "c1.mm"
include "cn0.mm"
include "wrdfin.mm"
include "hashcl.mm"
include "hashfzo0.mm"
include "syl.mm"
include "hashsng.mm"
include "oveq12d.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "syl5req.mm"
include "ofccat.mm"
include "cvv.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "wrdf.mm"
include "ovexd.mm"
include "ofcof.mm"
include "caddc.mm"
include "ccatlen.mm"
include "oveq2d.mm"
include "xpeq1d.mm"
include "eqid.mm"
include "ccatmulgnn0dir.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem ofcccat
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cK: class K
  assume ofcccat.1: |- ( ph -> F e. Word S )
  assume ofcccat.2: |- ( ph -> G e. Word S )
  assume ofcccat.3: |- ( ph -> K e. T )


  assert |- ( ph -> ( ( F ++ G ) oFC R K ) = ( ( F oFC R K ) ++ ( G oFC R K ) ) )

  proof
    wph
    cF
    cG
    cconcat
    co
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cK
    csn
    #
    cxp
    #
    cc0
    cG
    chash
    cfv
    #
    cfzo
    co
    #
    @3
    cxp
    #
    cconcat
    co
    #
    cR
    cof
    #
    co
    #
    cF
    @4
    @9
    co
    #
    cG
    @7
    @9
    co
    #
    cconcat
    co
    @0
    cK
    cR
    cofc
    #
    co
    #
    cF
    cK
    @13
    co
    #
    cG
    cK
    @13
    co
    #
    cconcat
    co
    wph
    cR
    cS
    cT
    cF
    cG
    @4
    @7
    ofcccat.1
    ofcccat.2
    wph
    cK
    cT
    wcel
    #
    @2
    cT
    @4
    wf
    @4
    cT
    cword
    #
    wcel
    ofcccat.3
    @2
    cK
    cT
    fconst6g
    cT
    @1
    @4
    iswrdi
    3syl
    wph
    @17
    @6
    cT
    @7
    wf
    @7
    @18
    wcel
    ofcccat.3
    @6
    cK
    cT
    fconst6g
    cT
    @5
    @7
    iswrdi
    3syl
    wph
    @4
    chash
    cfv
    #
    @2
    chash
    cfv
    #
    @3
    chash
    cfv
    #
    cmul
    co
    #
    @1
    @2
    cfn
    wcel
    #
    @3
    cfn
    wcel
    #
    @19
    @22
    wceq
    cc0
    @1
    fzofi
    #
    cK
    snfi
    #
    @2
    @3
    hashxp
    mp2an
    wph
    @22
    @1
    c1
    cmul
    co
    @1
    wph
    @20
    @1
    @21
    c1
    cmul
    wph
    @1
    cn0
    wcel
    #
    @20
    @1
    wceq
    wph
    cF
    cS
    cword
    #
    wcel
    #
    cF
    cfn
    wcel
    @27
    ofcccat.1
    cS
    cF
    wrdfin
    cF
    hashcl
    3syl
    #
    @1
    hashfzo0
    syl
    wph
    @17
    @21
    c1
    wceq
    ofcccat.3
    cK
    cT
    hashsng
    syl
    #
    oveq12d
    wph
    @1
    wph
    @1
    @30
    nn0cnd
    mulid1d
    eqtrd
    syl5req
    wph
    @7
    chash
    cfv
    #
    @6
    chash
    cfv
    #
    @21
    cmul
    co
    #
    @5
    @6
    cfn
    wcel
    #
    @24
    @32
    @34
    wceq
    cc0
    @5
    fzofi
    #
    @26
    @6
    @3
    hashxp
    mp2an
    wph
    @34
    @5
    c1
    cmul
    co
    @5
    wph
    @33
    @5
    @21
    c1
    cmul
    wph
    @5
    cn0
    wcel
    #
    @33
    @5
    wceq
    wph
    cG
    @28
    wcel
    #
    cG
    cfn
    wcel
    @37
    ofcccat.2
    cS
    cG
    wrdfin
    cG
    hashcl
    3syl
    #
    @5
    hashfzo0
    syl
    @31
    oveq12d
    wph
    @5
    wph
    @5
    @39
    nn0cnd
    mulid1d
    eqtrd
    syl5req
    ofccat
    wph
    @14
    @0
    cc0
    @0
    chash
    cfv
    #
    cfzo
    co
    #
    @3
    cxp
    #
    @9
    co
    @10
    wph
    @41
    cS
    cK
    cR
    @0
    cvv
    cT
    wph
    @0
    @28
    wcel
    #
    @41
    cS
    @0
    wf
    wph
    @29
    @38
    @43
    ofcccat.1
    ofcccat.2
    cS
    cF
    cG
    ccatcl
    syl2anc
    cS
    @0
    wrdf
    syl
    wph
    cc0
    @40
    cfzo
    ovexd
    ofcccat.3
    ofcof
    wph
    @42
    @8
    @0
    @9
    wph
    @42
    cc0
    @1
    @5
    caddc
    co
    #
    cfzo
    co
    #
    @3
    cxp
    #
    @8
    wph
    @41
    @45
    @3
    wph
    @40
    @44
    cc0
    cfzo
    wph
    @29
    @38
    @40
    @44
    wceq
    ofcccat.1
    ofcccat.2
    cS
    cF
    cG
    ccatlen
    syl2anc
    oveq2d
    xpeq1d
    wph
    @4
    @7
    @46
    cT
    cK
    @1
    @5
    @4
    eqid
    @7
    eqid
    @46
    eqid
    ofcccat.3
    @30
    @39
    ccatmulgnn0dir
    eqtr4d
    oveq2d
    eqtrd
    wph
    @15
    @11
    @16
    @12
    cconcat
    wph
    @2
    cS
    cK
    cR
    cF
    cfn
    cT
    wph
    @29
    @2
    cS
    cF
    wf
    ofcccat.1
    cS
    cF
    wrdf
    syl
    @23
    wph
    @25
    a1i
    ofcccat.3
    ofcof
    wph
    @6
    cS
    cK
    cR
    cG
    cfn
    cT
    wph
    @38
    @6
    cS
    cG
    wf
    ofcccat.2
    cS
    cG
    wrdf
    syl
    @35
    wph
    @36
    a1i
    ofcccat.3
    ofcof
    oveq12d
    3eqtr4d
end
