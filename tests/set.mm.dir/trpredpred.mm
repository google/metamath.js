include "cpred.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cuni.mm"
include "ctrpred.mm"
include "wss.mm"
include "wbr.mm"
include "wex.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "fr0g.mm"
include "wfn.mm"
include "wb.mm"
include "frfnom.mm"
include "peano1.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "sylib.mm"
include "0ex.mm"
include "breq1.mm"
include "spcev.mm"
include "syl.mm"
include "elrng.mm"
include "mpbird.mm"
include "elssuni.mm"
include "df-trpred.mm"
include "syl6sseqr.mm"

theorem trpredpred
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let va: setvar a
  let vy: setvar y
  let vz: setvar z


  assert |- ( Pred ( R , A , X ) e. B -> Pred ( R , A , X ) C_ TrPred ( R , A , X ) )

  proof
    cA
    cR
    cX
    cpred
    #
    cB
    wcel
    #
    @0
    va
    cvv
    vy
    va
    cv
    cA
    cR
    vy
    cv
    cpred
    ciun
    cmpt
    #
    @0
    crdg
    com
    cres
    #
    crn
    #
    cuni
    #
    cA
    cR
    cX
    ctrpred
    @1
    @0
    @4
    wcel
    #
    @0
    @5
    wss
    @1
    @6
    vz
    cv
    #
    @0
    @3
    wbr
    #
    vz
    wex
    #
    @1
    c0
    @0
    @3
    wbr
    #
    @9
    @1
    c0
    @3
    cfv
    @0
    wceq
    #
    @10
    @0
    cB
    @2
    fr0g
    @3
    com
    wfn
    c0
    com
    wcel
    @11
    @10
    wb
    @0
    @2
    frfnom
    peano1
    com
    c0
    @0
    @3
    fnbrfvb
    mp2an
    sylib
    @8
    @10
    vz
    c0
    0ex
    @7
    c0
    @0
    @3
    breq1
    spcev
    syl
    vz
    @0
    @3
    cB
    elrng
    mpbird
    @0
    @4
    elssuni
    syl
    vy
    cA
    cR
    cX
    va
    df-trpred
    syl6sseqr
end
