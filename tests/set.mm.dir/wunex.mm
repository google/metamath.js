include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cuni.mm"
include "cun.mm"
include "cpw.mm"
include "cpr.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "c1o.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "cwun.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "wunex2.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl.mm"

theorem wunex
  let vu: setvar u
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A e. V -> E. u e. WUni A C_ u )

  proof
    cA
    cV
    wcel
    vz
    cvv
    vz
    cv
    #
    @0
    cuni
    cun
    vx
    @0
    vx
    cv
    #
    cpw
    @1
    cuni
    cpr
    vy
    @0
    @1
    vy
    cv
    cpr
    cmpt
    crn
    cun
    ciun
    cun
    cmpt
    cA
    c1o
    cun
    crdg
    com
    cres
    #
    crn
    cuni
    #
    cwun
    wcel
    cA
    @3
    wss
    #
    wa
    cA
    vu
    cv
    #
    wss
    #
    vu
    cwun
    wrex
    vx
    vy
    vz
    cA
    @3
    @2
    cV
    @2
    eqid
    @3
    eqid
    wunex2
    @6
    @4
    vu
    @3
    cwun
    @5
    @3
    cA
    sseq2
    rspcev
    syl
end
