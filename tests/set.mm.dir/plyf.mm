include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "wf.mm"
include "wss.mm"
include "elply.mm"
include "simprbi.mm"
include "wa.mm"
include "fzfid.mm"
include "plybss.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "simplrr.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbid.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "sseldd.mm"
include "simpr.mm"
include "expcl.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem plyf
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cT: class T


  assert |- ( F e. ( Poly ` S ) -> F : CC --> CC )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    vz
    cc
    cc0
    vn
    cv
    #
    cfz
    co
    #
    vk
    cv
    #
    va
    cv
    #
    cfv
    #
    vz
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    va
    cS
    cc0
    csn
    #
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    vn
    cn0
    wrex
    #
    cc
    cc
    cF
    wf
    #
    @0
    cS
    cc
    wss
    @15
    vz
    cS
    vk
    vn
    cF
    va
    elply
    simprbi
    @0
    @11
    @16
    vn
    va
    cn0
    @14
    @0
    @1
    cn0
    wcel
    #
    @4
    @14
    wcel
    #
    wa
    #
    wa
    #
    @16
    @11
    cc
    cc
    @10
    wf
    @20
    vz
    cc
    @9
    cc
    @10
    @20
    @6
    cc
    wcel
    #
    wa
    #
    @2
    @8
    vk
    @22
    cc0
    @1
    fzfid
    @22
    @3
    @2
    wcel
    #
    wa
    #
    @5
    @7
    @24
    @13
    cc
    @5
    @22
    @13
    cc
    wss
    #
    @23
    @0
    @25
    @19
    @21
    @0
    cS
    @12
    cc
    cS
    cF
    plybss
    @0
    cc0
    cc
    @0
    0cnd
    snssd
    unssd
    ad2antrr
    #
    adantr
    @22
    cn0
    @13
    @4
    wf
    #
    @3
    cn0
    wcel
    #
    @5
    @13
    wcel
    @23
    @22
    @18
    @27
    @0
    @17
    @18
    @21
    simplrr
    @22
    @13
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    @18
    @27
    wb
    @22
    @25
    cc
    cvv
    wcel
    @29
    @26
    cnex
    @13
    cc
    cvv
    ssexg
    sylancl
    nn0ex
    @13
    cn0
    @4
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    @3
    @1
    elfznn0
    #
    cn0
    @13
    @3
    @4
    ffvelrn
    syl2an
    sseldd
    @22
    @21
    @28
    @7
    cc
    wcel
    @23
    @20
    @21
    simpr
    @30
    @6
    @3
    expcl
    syl2an
    mulcld
    fsumcl
    @10
    eqid
    fmptd
    cc
    cc
    cF
    @10
    feq1
    syl5ibrcom
    rexlimdvva
    mpd
end
