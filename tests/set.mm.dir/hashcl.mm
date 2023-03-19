include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "chash.mm"
include "cn0.mm"
include "eqid.mm"
include "hashgval.mm"
include "ficardom.mm"
include "wf1o.mm"
include "wf.mm"
include "hashgf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem hashcl
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Fin -> ( # ` A ) e. NN0 )

  proof
    cA
    cfn
    wcel
    #
    cA
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
    cA
    chash
    cfv
    cn0
    vx
    cA
    @2
    @2
    eqid
    #
    hashgval
    @0
    @1
    com
    wcel
    @3
    cn0
    wcel
    cA
    ficardom
    com
    cn0
    @1
    @2
    com
    cn0
    @2
    wf1o
    com
    cn0
    @2
    wf
    vx
    @2
    @4
    hashgf1o
    com
    cn0
    @2
    f1of
    ax-mp
    ffvelrni
    syl
    eqeltrrd
end
