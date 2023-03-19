include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "creverse.mm"
include "wfn.mm"
include "wf.mm"
include "revcl.mm"
include "wrdf.mm"
include "ffn.mm"
include "4syl.mm"
include "wceq.mm"
include "revlen.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "wrdfn.mm"
include "cv.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "adantr.mm"
include "simpr.mm"
include "eleqtrrd.mm"
include "revfv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "cfz.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "fznn0sub2.mm"
include "syldan.mm"
include "cc.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "elfzoelz.mm"
include "nncan.mm"
include "syl2an.mm"
include "eqfnfvd.mm"

theorem revrev
  let cA: class A
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let cX: class X
  let cS: class S
  let cT: class T


  assert |- ( W e. Word A -> ( reverse ` ( reverse ` W ) ) = W )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    vx
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cW
    creverse
    cfv
    #
    creverse
    cfv
    #
    cW
    @1
    @5
    cc0
    @5
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @5
    @3
    wfn
    @1
    @4
    @0
    wcel
    #
    @5
    @0
    wcel
    @7
    cA
    @5
    wf
    @8
    cA
    cW
    revcl
    #
    cA
    @4
    revcl
    cA
    @5
    wrdf
    @7
    cA
    @5
    ffn
    4syl
    @1
    @7
    @3
    @5
    @1
    @6
    @2
    cc0
    cfzo
    @1
    @6
    @4
    chash
    cfv
    #
    @2
    @1
    @9
    @6
    @11
    wceq
    @10
    cA
    @4
    revlen
    syl
    cA
    cW
    revlen
    #
    eqtrd
    oveq2d
    fneq2d
    mpbid
    cA
    cW
    wrdfn
    @1
    vx
    cv
    #
    @3
    wcel
    #
    wa
    #
    @13
    @5
    cfv
    #
    @11
    c1
    cmin
    co
    #
    @13
    cmin
    co
    #
    @4
    cfv
    #
    @13
    cW
    cfv
    #
    @15
    @9
    @13
    cc0
    @11
    cfzo
    co
    #
    wcel
    @16
    @19
    wceq
    @1
    @9
    @14
    @10
    adantr
    @15
    @13
    @3
    @21
    @1
    @14
    simpr
    @15
    @11
    @2
    cc0
    cfzo
    @1
    @11
    @2
    wceq
    @14
    @12
    adantr
    #
    oveq2d
    eleqtrrd
    cA
    @4
    @13
    revfv
    syl2anc
    @15
    @19
    @2
    c1
    cmin
    co
    #
    @13
    cmin
    co
    #
    @4
    cfv
    #
    @20
    @15
    @18
    @24
    @4
    @15
    @17
    @23
    @13
    cmin
    @15
    @11
    @2
    c1
    cmin
    @22
    oveq1d
    oveq1d
    fveq2d
    @15
    @25
    @23
    @24
    cmin
    co
    #
    cW
    cfv
    #
    @20
    @1
    @14
    @24
    @3
    wcel
    @25
    @27
    wceq
    @15
    @24
    cc0
    @23
    cfz
    co
    #
    @3
    @15
    @13
    @28
    wcel
    #
    @24
    @28
    wcel
    @1
    @14
    @29
    @1
    @3
    @28
    @13
    @1
    @2
    cz
    wcel
    #
    @3
    @28
    wceq
    #
    @1
    @2
    cA
    cW
    lencl
    nn0zd
    #
    cc0
    @2
    fzoval
    syl
    #
    eleq2d
    biimpa
    @13
    @23
    fznn0sub2
    syl
    @1
    @31
    @14
    @33
    adantr
    eleqtrrd
    cA
    cW
    @24
    revfv
    syldan
    @15
    @26
    @13
    cW
    @1
    @23
    cc
    wcel
    @13
    cc
    wcel
    @26
    @13
    wceq
    @14
    @1
    @23
    @1
    @30
    @23
    cz
    wcel
    @32
    @2
    peano2zm
    syl
    zcnd
    @14
    @13
    @13
    cc0
    @2
    elfzoelz
    zcnd
    @23
    @13
    nncan
    syl2an
    fveq2d
    eqtrd
    eqtrd
    eqtrd
    eqfnfvd
end
