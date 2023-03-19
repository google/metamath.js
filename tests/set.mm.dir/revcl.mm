include "cword.mm"
include "wcel.mm"
include "creverse.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "revval.mm"
include "wf.mm"
include "wa.mm"
include "wrdf.mm"
include "adantr.mm"
include "cfz.mm"
include "simpr.mm"
include "cz.mm"
include "wceq.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "syl.mm"
include "eleqtrd.mm"
include "fznn0sub2.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "iswrdi.mm"
include "eqeltrd.mm"

theorem revcl
  let cA: class A
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let cX: class X


  assert |- ( W e. Word A -> ( reverse ` W ) e. Word A )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    cW
    creverse
    cfv
    vx
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    @2
    c1
    cmin
    co
    #
    vx
    cv
    #
    cmin
    co
    #
    cW
    cfv
    #
    cmpt
    #
    @0
    vx
    @0
    cW
    revval
    @1
    @3
    cA
    @8
    wf
    @8
    @0
    wcel
    @1
    vx
    @3
    @7
    cA
    @8
    @1
    @5
    @3
    wcel
    #
    wa
    #
    @3
    cA
    @6
    cW
    @1
    @3
    cA
    cW
    wf
    @9
    cA
    cW
    wrdf
    adantr
    @10
    @6
    cc0
    @4
    cfz
    co
    #
    @3
    @10
    @5
    @11
    wcel
    @6
    @11
    wcel
    @10
    @5
    @3
    @11
    @1
    @9
    simpr
    @10
    @2
    cz
    wcel
    @3
    @11
    wceq
    @10
    @2
    @1
    @2
    cn0
    wcel
    @9
    cA
    cW
    lencl
    adantr
    nn0zd
    cc0
    @2
    fzoval
    syl
    #
    eleqtrd
    @5
    @4
    fznn0sub2
    syl
    @12
    eleqtrrd
    ffvelrnd
    @8
    eqid
    fmptd
    cA
    @2
    @8
    iswrdi
    syl
    eqeltrd
end
