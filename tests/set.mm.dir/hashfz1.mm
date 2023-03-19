include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "ccrd.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "ccnv.mm"
include "chash.mm"
include "eqid.mm"
include "cardfz.mm"
include "fveq2d.mm"
include "cfn.mm"
include "wceq.mm"
include "fzfid.mm"
include "hashgval.mm"
include "syl.mm"
include "wf1o.mm"
include "hashgf1o.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"
include "3eqtr3d.mm"

theorem hashfz1
  let cN: class N
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- ( N e. NN0 -> ( # ` ( 1 ... N ) ) = N )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    ccrd
    cfv
    #
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    cfv
    #
    cN
    @3
    ccnv
    cfv
    #
    @3
    cfv
    #
    @1
    chash
    cfv
    #
    cN
    @0
    @2
    @5
    @3
    vx
    @3
    cN
    @3
    eqid
    #
    cardfz
    fveq2d
    @0
    @1
    cfn
    wcel
    @4
    @7
    wceq
    @0
    c1
    cN
    fzfid
    vx
    @1
    @3
    @8
    hashgval
    syl
    com
    cn0
    @3
    wf1o
    @0
    @6
    cN
    wceq
    vx
    @3
    @8
    hashgf1o
    com
    cn0
    cN
    @3
    f1ocnvfv2
    mpan
    3eqtr3d
end
