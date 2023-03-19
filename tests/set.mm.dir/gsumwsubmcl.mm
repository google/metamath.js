include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cword.mm"
include "wa.mm"
include "cgsu.mm"
include "co.mm"
include "c0g.mm"
include "c0.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "gsum0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "wne.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cplusg.mm"
include "cc0.mm"
include "cseq.mm"
include "cbs.mm"
include "cmnd.mm"
include "submrcl.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "cuz.mm"
include "cn.mm"
include "lennncl.mm"
include "adantll.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "cfzo.mm"
include "wf.mm"
include "wrdf.mm"
include "ad2antlr.mm"
include "cz.mm"
include "nnzd.mm"
include "fzoval.mm"
include "feq2d.mm"
include "mpbid.mm"
include "wss.mm"
include "submss.mm"
include "fssd.mm"
include "gsumval2.mm"
include "cv.mm"
include "ffvelrnda.mm"
include "simpll.mm"
include "submcl.mm"
include "3expb.mm"
include "sylan.mm"
include "seqcl.mm"
include "eqeltrd.mm"
include "subm0cl.mm"
include "adantr.mm"
include "pm2.61ne.mm"

theorem gsumwsubmcl
  let cS: class S
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S e. ( SubMnd ` G ) /\ W e. Word S ) -> ( G gsum W ) e. S )

  proof
    cS
    cG
    csubmnd
    cfv
    wcel
    #
    cW
    cS
    cword
    wcel
    #
    wa
    #
    cG
    cW
    cgsu
    co
    #
    cS
    wcel
    cG
    c0g
    cfv
    #
    cS
    wcel
    #
    cW
    c0
    cW
    c0
    wceq
    #
    @3
    @4
    cS
    @6
    @3
    cG
    c0
    cgsu
    co
    @4
    cW
    c0
    cG
    cgsu
    oveq2
    cG
    @4
    @4
    eqid
    #
    gsum0
    syl6eq
    eleq1d
    @2
    cW
    c0
    wne
    #
    wa
    #
    @3
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cG
    cplusg
    cfv
    #
    cW
    cc0
    cseq
    cfv
    cS
    @9
    cG
    cbs
    cfv
    #
    @12
    cW
    cG
    cc0
    @11
    cmnd
    @13
    eqid
    #
    @12
    eqid
    #
    @0
    cG
    cmnd
    wcel
    @1
    @8
    cS
    cG
    submrcl
    ad2antrr
    @9
    @11
    cn0
    cc0
    cuz
    cfv
    @9
    @10
    cn
    wcel
    #
    @11
    cn0
    wcel
    @1
    @8
    @16
    @0
    cS
    cW
    lennncl
    adantll
    #
    @10
    nnm1nn0
    syl
    nn0uz
    syl6eleq
    #
    @9
    cc0
    @11
    cfz
    co
    #
    cS
    @13
    cW
    @9
    cc0
    @10
    cfzo
    co
    #
    cS
    cW
    wf
    #
    @19
    cS
    cW
    wf
    @1
    @21
    @0
    @8
    cS
    cW
    wrdf
    ad2antlr
    @9
    @20
    @19
    cS
    cW
    @9
    @10
    cz
    wcel
    @20
    @19
    wceq
    @9
    @10
    @17
    nnzd
    cc0
    @10
    fzoval
    syl
    feq2d
    mpbid
    #
    @0
    cS
    @13
    wss
    @1
    @8
    @13
    cS
    cG
    @14
    submss
    ad2antrr
    fssd
    gsumval2
    @9
    vx
    vy
    @12
    cS
    cW
    cc0
    @11
    @18
    @9
    @19
    cS
    vx
    cv
    #
    cW
    @22
    ffvelrnda
    @9
    @0
    @23
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    @23
    @25
    @12
    co
    cS
    wcel
    #
    @0
    @1
    @8
    simpll
    @0
    @24
    @26
    @27
    @12
    cS
    cG
    @23
    @25
    @15
    submcl
    3expb
    sylan
    seqcl
    eqeltrd
    @0
    @5
    @1
    cS
    cG
    @4
    @7
    subm0cl
    adantr
    pm2.61ne
end
