include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "ssdomg.mm"
include "imp.mm"
include "3adant3.mm"
include "csuc.mm"
include "cdif.mm"
include "cint.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "wf1.mm"
include "simp1.mm"
include "ssexg.mm"
include "ancoms.mm"
include "eqid.mm"
include "unblem4.mm"
include "3adant1.mm"
include "f1dom2g.mm"
include "syl3anc.mm"
include "sbth.mm"
include "syl2anc.mm"

theorem unbnn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( _om e. _V /\ A C_ _om /\ A. x e. _om E. y e. A x e. y ) -> A ~~ _om )

  proof
    com
    cvv
    wcel
    #
    cA
    com
    wss
    #
    vx
    cv
    vy
    cv
    wcel
    vy
    cA
    wrex
    vx
    com
    wral
    #
    w3a
    #
    cA
    com
    cdom
    wbr
    #
    com
    cA
    cdom
    wbr
    #
    cA
    com
    cen
    wbr
    @0
    @1
    @4
    @2
    @0
    @1
    @4
    cA
    com
    cvv
    ssdomg
    imp
    3adant3
    @3
    @0
    cA
    cvv
    wcel
    #
    com
    cA
    vz
    cvv
    cA
    vz
    cv
    csuc
    cdif
    cint
    cmpt
    cA
    cint
    crdg
    com
    cres
    #
    wf1
    #
    @5
    @0
    @1
    @2
    simp1
    @0
    @1
    @6
    @2
    @1
    @0
    @6
    cA
    com
    cvv
    ssexg
    ancoms
    3adant3
    @1
    @2
    @8
    @0
    vz
    vx
    vy
    cA
    @7
    @7
    eqid
    unblem4
    3adant1
    com
    cA
    @7
    cvv
    cvv
    f1dom2g
    syl3anc
    cA
    com
    sbth
    syl2anc
end
