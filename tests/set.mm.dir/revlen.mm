include "cword.mm"
include "wcel.mm"
include "creverse.mm"
include "cfv.mm"
include "chash.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "revval.mm"
include "fveq2d.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "wa.mm"
include "wrdf.mm"
include "adantr.mm"
include "cfz.mm"
include "simpr.mm"
include "cn0.mm"
include "cz.mm"
include "lencl.mm"
include "nn0z.mm"
include "fzoval.mm"
include "3syl.mm"
include "eleqtrd.mm"
include "fznn0sub2.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffn.mm"
include "hashfn.mm"
include "hashfzo0.mm"
include "3eqtrd.mm"

theorem revlen
  let cA: class A
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let cX: class X


  assert |- ( W e. Word A -> ( # ` ( reverse ` W ) ) = ( # ` W ) )

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
    #
    chash
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
    @3
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
    chash
    cfv
    #
    @4
    chash
    cfv
    #
    @3
    @1
    @2
    @9
    chash
    vx
    @0
    cW
    revval
    fveq2d
    @1
    @4
    cA
    @9
    wf
    @9
    @4
    wfn
    @10
    @11
    wceq
    @1
    vx
    @4
    @8
    cA
    @9
    @1
    @6
    @4
    wcel
    #
    wa
    #
    @4
    cA
    @7
    cW
    @1
    @4
    cA
    cW
    wf
    @12
    cA
    cW
    wrdf
    adantr
    @13
    @7
    cc0
    @5
    cfz
    co
    #
    @4
    @13
    @6
    @14
    wcel
    @7
    @14
    wcel
    @13
    @6
    @4
    @14
    @1
    @12
    simpr
    @13
    @3
    cn0
    wcel
    #
    @3
    cz
    wcel
    @4
    @14
    wceq
    @1
    @15
    @12
    cA
    cW
    lencl
    #
    adantr
    @3
    nn0z
    cc0
    @3
    fzoval
    3syl
    #
    eleqtrd
    @6
    @5
    fznn0sub2
    syl
    @17
    eleqtrrd
    ffvelrnd
    @9
    eqid
    fmptd
    @4
    cA
    @9
    ffn
    @4
    @9
    hashfn
    3syl
    @1
    @15
    @11
    @3
    wceq
    @16
    @3
    hashfzo0
    syl
    3eqtrd
end
