include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cneg.mm"
include "cmpt.mm"
include "ccom.mm"
include "cfv.mm"
include "cncff.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "negeq.mm"
include "fmptco.mm"
include "syl6eqr.mm"
include "id.mm"
include "wss.mm"
include "ssid.mm"
include "eqid.mm"
include "negcncf.mm"
include "mp1i.mm"
include "cncfco.mm"
include "eqeltrrd.mm"

theorem negfcncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume negfcncf.1: |- G = ( x e. A |-> -u ( F ` x ) )

  disjoint F x
  disjoint A x
  disjoint x y
  disjoint F y
  assert |- ( F e. ( A -cn-> CC ) -> G e. ( A -cn-> CC ) )

  proof
    cF
    cA
    cc
    ccncf
    co
    #
    wcel
    #
    vy
    cc
    vy
    cv
    #
    cneg
    #
    cmpt
    #
    cF
    ccom
    #
    cG
    @0
    @1
    @5
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    cG
    @1
    vx
    vy
    cA
    cc
    @7
    @3
    @8
    cF
    @4
    @1
    cA
    cc
    @6
    cF
    cA
    cc
    cF
    cncff
    #
    ffvelrnda
    @1
    vx
    cA
    cc
    cF
    @9
    feqmptd
    @1
    @4
    eqidd
    @2
    @7
    negeq
    fmptco
    negfcncf.1
    syl6eqr
    @1
    cA
    cc
    cc
    cF
    @4
    @1
    id
    cc
    cc
    wss
    @4
    cc
    cc
    ccncf
    co
    wcel
    @1
    cc
    ssid
    vy
    cc
    @4
    @4
    eqid
    negcncf
    mp1i
    cncfco
    eqeltrrd
end
