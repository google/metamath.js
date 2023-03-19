include "wcel.mm"
include "w3a.mm"
include "ccnfld.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cfv.mm"
include "cc.mm"
include "cc0.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cnfldadd.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "simp1.mm"
include "wf.mm"
include "wa.mm"
include "cn0.mm"
include "wss.mm"
include "psrbagf.mm"
include "nn0sscn.mm"
include "fss.mm"
include "sylancl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "cfsupp.mm"
include "wbr.mm"
include "psrbagfsupp.mm"
include "ancoms.mm"
include "gsumadd.mm"
include "wceq.mm"
include "psrbagaddcl.mm"
include "cv.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3adant1.mm"
include "3eqtr4d.mm"

theorem tdeglem3
  let cA: class A
  let vh: setvar h
  let vm: setvar m
  let cH: class H
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tdeglem.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume tdeglem.h: |- H = ( h e. A |-> ( CCfld gsum h ) )

  disjoint A h
  disjoint I h
  disjoint I m
  disjoint h m
  disjoint V h
  disjoint X h
  disjoint X m
  disjoint Y h
  disjoint Y m
  disjoint A x
  disjoint A y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint V x
  disjoint V y
  assert |- ( ( I e. V /\ X e. A /\ Y e. A ) -> ( H ` ( X oF + Y ) ) = ( ( H ` X ) + ( H ` Y ) ) )

  proof
    cI
    cV
    wcel
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    w3a
    #
    ccnfld
    cX
    cY
    caddc
    cof
    co
    #
    cgsu
    co
    #
    ccnfld
    cX
    cgsu
    co
    #
    ccnfld
    cY
    cgsu
    co
    #
    caddc
    co
    #
    @4
    cH
    cfv
    #
    cX
    cH
    cfv
    #
    cY
    cH
    cfv
    #
    caddc
    co
    #
    @3
    cI
    cc
    caddc
    cX
    ccnfld
    cY
    cV
    cc0
    cnfldbas
    cnfld0
    cnfldadd
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
    @1
    @2
    simp1
    @0
    @1
    cI
    cc
    cX
    wf
    #
    @2
    @0
    @1
    wa
    cI
    cn0
    cX
    wf
    cn0
    cc
    wss
    #
    @13
    cA
    vm
    cX
    cI
    cV
    tdeglem.a
    psrbagf
    nn0sscn
    cI
    cn0
    cc
    cX
    fss
    sylancl
    3adant3
    @0
    @2
    cI
    cc
    cY
    wf
    #
    @1
    @0
    @2
    wa
    cI
    cn0
    cY
    wf
    @14
    @15
    cA
    vm
    cY
    cI
    cV
    tdeglem.a
    psrbagf
    nn0sscn
    cI
    cn0
    cc
    cY
    fss
    sylancl
    3adant2
    @0
    @1
    cX
    cc0
    cfsupp
    wbr
    #
    @2
    @1
    @0
    @16
    cA
    vm
    cI
    cV
    cX
    tdeglem.a
    psrbagfsupp
    ancoms
    3adant3
    @0
    @2
    cY
    cc0
    cfsupp
    wbr
    #
    @1
    @2
    @0
    @17
    cA
    vm
    cI
    cV
    cY
    tdeglem.a
    psrbagfsupp
    ancoms
    3adant2
    gsumadd
    @3
    @4
    cA
    wcel
    @9
    @5
    wceq
    cA
    vm
    cX
    cY
    cI
    cV
    tdeglem.a
    psrbagaddcl
    vh
    @4
    ccnfld
    vh
    cv
    #
    cgsu
    co
    #
    @5
    cA
    cH
    @18
    @4
    ccnfld
    cgsu
    oveq2
    tdeglem.h
    ccnfld
    @4
    cgsu
    ovex
    fvmpt
    syl
    @1
    @2
    @12
    @8
    wceq
    @0
    @1
    @2
    @10
    @6
    @11
    @7
    caddc
    vh
    cX
    @19
    @6
    cA
    cH
    @18
    cX
    ccnfld
    cgsu
    oveq2
    tdeglem.h
    ccnfld
    cX
    cgsu
    ovex
    fvmpt
    vh
    cY
    @19
    @7
    cA
    cH
    @18
    cY
    ccnfld
    cgsu
    oveq2
    tdeglem.h
    ccnfld
    cY
    cgsu
    ovex
    fvmpt
    oveqan12d
    3adant1
    3eqtr4d
end
