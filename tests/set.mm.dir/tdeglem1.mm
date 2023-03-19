include "wcel.mm"
include "ccnfld.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cnfld0.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "simpl.mm"
include "csubmnd.mm"
include "cfv.mm"
include "nn0subm.mm"
include "a1i.mm"
include "psrbagf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "psrbagfsupp.mm"
include "ancoms.mm"
include "gsumsubmcl.mm"
include "fmptd.mm"

theorem tdeglem1
  let cA: class A
  let vh: setvar h
  let vm: setvar m
  let cH: class H
  let cI: class I
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tdeglem.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume tdeglem.h: |- H = ( h e. A |-> ( CCfld gsum h ) )

  disjoint A h
  disjoint I h
  disjoint I m
  disjoint h m
  disjoint V h
  disjoint A x
  disjoint A y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint V x
  disjoint V y
  assert |- ( I e. V -> H : A --> NN0 )

  proof
    cI
    cV
    wcel
    #
    vh
    cA
    ccnfld
    vh
    cv
    #
    cgsu
    co
    cn0
    cH
    @0
    @1
    cA
    wcel
    #
    wa
    #
    cI
    cn0
    @1
    ccnfld
    cV
    cc0
    cnfld0
    ccnfld
    crg
    wcel
    ccnfld
    ccmn
    wcel
    @3
    cnring
    ccnfld
    ringcmn
    mp1i
    @0
    @2
    simpl
    cn0
    ccnfld
    csubmnd
    cfv
    wcel
    @3
    nn0subm
    a1i
    cA
    vm
    @1
    cI
    cV
    tdeglem.a
    psrbagf
    @2
    @0
    @1
    cc0
    cfsupp
    wbr
    cA
    vm
    cI
    cV
    @1
    tdeglem.a
    psrbagfsupp
    ancoms
    gsumsubmcl
    tdeglem.h
    fmptd
end
