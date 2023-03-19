include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "0ex.mm"
include "restval.mm"
include "mpan2.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "in0.mm"
include "elsn2.mm"
include "mpbir.mm"
include "a1i.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "eqsstrd.mm"
include "resttop.mm"
include "0opn.mm"
include "snssd.mm"
include "eqssd.mm"

theorem rest0
  let cJ: class J
  let vx: setvar x


  assert |- ( J e. Top -> ( J |`t (/) ) = { (/) } )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    c0
    crest
    co
    #
    c0
    csn
    #
    @0
    @1
    vx
    cJ
    vx
    cv
    #
    c0
    cin
    #
    cmpt
    #
    crn
    #
    @2
    @0
    c0
    cvv
    wcel
    #
    @1
    @6
    wceq
    0ex
    vx
    c0
    cJ
    ctop
    cvv
    restval
    mpan2
    @0
    cJ
    @2
    @5
    wf
    @6
    @2
    wss
    @0
    vx
    cJ
    @4
    @2
    @5
    @4
    @2
    wcel
    #
    @0
    @3
    cJ
    wcel
    wa
    @8
    @4
    c0
    wceq
    @3
    in0
    @4
    c0
    0ex
    elsn2
    mpbir
    a1i
    @5
    eqid
    fmptd
    cJ
    @2
    @5
    frn
    syl
    eqsstrd
    @0
    c0
    @1
    @0
    @1
    ctop
    wcel
    #
    c0
    @1
    wcel
    @0
    @7
    @9
    0ex
    c0
    cJ
    cvv
    resttop
    mpan2
    @1
    0opn
    syl
    snssd
    eqssd
end
