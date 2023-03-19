include "cplusg.mm"
include "cfv.mm"
include "cvsca.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "clmod.mm"
include "cbs.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "csca.mm"
include "cmulr.mm"
include "clfn.mm"
include "cvv.mm"
include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "lmodring.mm"
include "syl.mm"
include "ringcl.mm"
include "3expb.mm"
include "sylan.mm"
include "wf.mm"
include "lflf.mm"
include "syl2anc.mm"
include "fconst6g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "inidm.mm"
include "off.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "lfli.mm"
include "syl113anc.mm"
include "oveq1d.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "ringass.mm"
include "3eqtrd.mm"
include "lmodvscl.mm"
include "lmodvacl.mm"
include "wfn.mm"
include "ffn.mm"
include "ofc2.mm"
include "syldan.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "islfld.mm"

theorem lflvscl
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lflsccl.v: |- V = ( Base ` W )
  assume lflsccl.d: |- D = ( Scalar ` W )
  assume lflsccl.k: |- K = ( Base ` D )
  assume lflsccl.t: |- .x. = ( .r ` D )
  assume lflsccl.f: |- F = ( LFnl ` W )
  assume lflsccl.w: |- ( ph -> W e. LMod )
  assume lflsccl.g: |- ( ph -> G e. F )
  assume lflsccl.r: |- ( ph -> R e. K )


  assert |- ( ph -> ( G oF .x. ( V X. { R } ) ) e. F )

  proof
    wph
    vx
    vy
    cD
    cW
    cplusg
    cfv
    #
    cD
    cplusg
    cfv
    #
    cW
    cvsca
    cfv
    #
    c.x
    cF
    cG
    cV
    cR
    csn
    cxp
    #
    c.x
    cof
    co
    #
    cK
    cV
    cW
    clmod
    vr
    cV
    cW
    cbs
    cfv
    #
    wceq
    wph
    lflsccl.v
    a1i
    wph
    @0
    eqidd
    cD
    cW
    csca
    cfv
    wceq
    wph
    lflsccl.d
    a1i
    wph
    @2
    eqidd
    cK
    cD
    cbs
    cfv
    wceq
    wph
    lflsccl.k
    a1i
    wph
    @1
    eqidd
    c.x
    cD
    cmulr
    cfv
    wceq
    wph
    lflsccl.t
    a1i
    cF
    cW
    clfn
    cfv
    wceq
    wph
    lflsccl.f
    a1i
    wph
    vx
    vy
    cV
    cV
    cV
    c.x
    cK
    cK
    cK
    cG
    @3
    cvv
    cvv
    wph
    cD
    crg
    wcel
    #
    vx
    cv
    #
    cK
    wcel
    #
    vy
    cv
    #
    cK
    wcel
    #
    wa
    @7
    @9
    c.x
    co
    cK
    wcel
    #
    wph
    cW
    clmod
    wcel
    #
    @6
    lflsccl.w
    cD
    cW
    lflsccl.d
    lmodring
    syl
    #
    @6
    @8
    @10
    @11
    cK
    cD
    c.x
    @7
    @9
    lflsccl.k
    lflsccl.t
    ringcl
    3expb
    sylan
    wph
    @12
    cG
    cF
    wcel
    #
    cV
    cK
    cG
    wf
    #
    lflsccl.w
    lflsccl.g
    cD
    cF
    cG
    cK
    cV
    cW
    clmod
    lflsccl.d
    lflsccl.k
    lflsccl.v
    lflsccl.f
    lflf
    syl2anc
    #
    wph
    cR
    cK
    wcel
    #
    cV
    cK
    @3
    wf
    lflsccl.r
    cV
    cR
    cK
    fconst6g
    syl
    cV
    cvv
    wcel
    wph
    cV
    @5
    cvv
    lflsccl.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    #
    @18
    cV
    inidm
    off
    wph
    vr
    cv
    #
    cK
    wcel
    #
    @7
    cV
    wcel
    #
    @9
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @19
    @7
    @2
    co
    #
    @9
    @0
    co
    #
    cG
    cfv
    #
    cR
    c.x
    co
    #
    @19
    @7
    cG
    cfv
    #
    cR
    c.x
    co
    #
    c.x
    co
    #
    @9
    cG
    cfv
    #
    cR
    c.x
    co
    #
    @1
    co
    #
    @26
    @4
    cfv
    #
    @19
    @7
    @4
    cfv
    #
    c.x
    co
    #
    @9
    @4
    cfv
    #
    @1
    co
    @24
    @28
    @19
    @29
    c.x
    co
    #
    @32
    @1
    co
    #
    cR
    c.x
    co
    #
    @39
    cR
    c.x
    co
    #
    @33
    @1
    co
    #
    @34
    @24
    @27
    @40
    cR
    c.x
    @24
    @12
    @14
    @20
    @21
    @22
    @27
    @40
    wceq
    wph
    @12
    @23
    lflsccl.w
    adantr
    #
    wph
    @14
    @23
    lflsccl.g
    adantr
    #
    wph
    @20
    @21
    @22
    simpr1
    #
    wph
    @20
    @21
    @22
    simpr2
    #
    wph
    @20
    @21
    @22
    simpr3
    #
    cD
    @0
    @1
    @19
    @2
    c.x
    cF
    cG
    cK
    cV
    cW
    @7
    @9
    clmod
    lflsccl.v
    @0
    eqid
    #
    lflsccl.d
    @2
    eqid
    #
    lflsccl.k
    @1
    eqid
    #
    lflsccl.t
    lflsccl.f
    lfli
    syl113anc
    oveq1d
    @24
    @6
    @39
    cK
    wcel
    #
    @32
    cK
    wcel
    #
    @17
    @41
    @43
    wceq
    wph
    @6
    @23
    @13
    adantr
    #
    @24
    @6
    @20
    @29
    cK
    wcel
    #
    @52
    @54
    @46
    @24
    @12
    @14
    @21
    @55
    @44
    @45
    @47
    cD
    cF
    cG
    cK
    cV
    cW
    @7
    clmod
    lflsccl.d
    lflsccl.k
    lflsccl.v
    lflsccl.f
    lflcl
    syl3anc
    #
    cK
    cD
    c.x
    @19
    @29
    lflsccl.k
    lflsccl.t
    ringcl
    syl3anc
    @24
    @12
    @14
    @22
    @53
    @44
    @45
    @48
    cD
    cF
    cG
    cK
    cV
    cW
    @9
    clmod
    lflsccl.d
    lflsccl.k
    lflsccl.v
    lflsccl.f
    lflcl
    syl3anc
    wph
    @17
    @23
    lflsccl.r
    adantr
    #
    cK
    @1
    cD
    c.x
    @39
    @32
    cR
    lflsccl.k
    @51
    lflsccl.t
    ringdir
    syl13anc
    @24
    @42
    @31
    @33
    @1
    @24
    @6
    @20
    @55
    @17
    @42
    @31
    wceq
    @54
    @46
    @56
    @57
    cK
    cD
    c.x
    @19
    @29
    cR
    lflsccl.k
    lflsccl.t
    ringass
    syl13anc
    oveq1d
    3eqtrd
    wph
    @23
    @26
    cV
    wcel
    #
    @35
    @28
    wceq
    @24
    @12
    @25
    cV
    wcel
    #
    @22
    @58
    @44
    @24
    @12
    @20
    @21
    @59
    @44
    @46
    @47
    @19
    @2
    cD
    cK
    cV
    cW
    @7
    lflsccl.v
    lflsccl.d
    @50
    lflsccl.k
    lmodvscl
    syl3anc
    @48
    @0
    cV
    cW
    @25
    @9
    lflsccl.v
    @49
    lmodvacl
    syl3anc
    wph
    cV
    cR
    @27
    c.x
    cG
    cvv
    cK
    @26
    @18
    lflsccl.r
    wph
    @15
    cG
    cV
    wfn
    @16
    cV
    cK
    cG
    ffn
    syl
    #
    wph
    @58
    wa
    @27
    eqidd
    ofc2
    syldan
    @24
    @37
    @31
    @38
    @33
    @1
    @24
    @36
    @30
    @19
    c.x
    wph
    @23
    @21
    @36
    @30
    wceq
    @47
    wph
    cV
    cR
    @29
    c.x
    cG
    cvv
    cK
    @7
    @18
    lflsccl.r
    @60
    wph
    @21
    wa
    @29
    eqidd
    ofc2
    syldan
    oveq2d
    wph
    @23
    @22
    @38
    @33
    wceq
    @48
    wph
    cV
    cR
    @32
    c.x
    cG
    cvv
    cK
    @9
    @18
    lflsccl.r
    @60
    wph
    @22
    wa
    @32
    eqidd
    ofc2
    syldan
    oveq12d
    3eqtr4d
    lflsccl.w
    islfld
end
