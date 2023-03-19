include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "zmulcl.mm"
include "anim1i.mm"
include "3impa.mm"
include "3simpb.mm"
include "ancoms.mm"
include "3ad2antl2.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "mulass.mm"
include "mul32.mm"
include "eqtr3d.mm"
include "syl3an.mm"
include "3coml.mm"
include "3expa.mm"
include "3adantl3.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "dvds1lem.mm"

theorem muldvds1
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K x. M ) || N -> K || N ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    vx
    cK
    cM
    cmul
    co
    #
    cN
    cK
    cN
    vx
    cv
    #
    cM
    cmul
    co
    #
    @0
    @1
    @2
    @4
    cz
    wcel
    #
    @2
    wa
    @0
    @1
    wa
    @7
    @2
    cK
    cM
    zmulcl
    anim1i
    3impa
    @0
    @1
    @2
    3simpb
    @1
    @0
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @2
    @8
    @1
    @9
    @5
    cM
    zmulcl
    ancoms
    3ad2antl2
    @3
    @8
    wa
    #
    @5
    @4
    cmul
    co
    #
    cN
    wceq
    @6
    cK
    cmul
    co
    #
    cN
    wceq
    @10
    @11
    @12
    cN
    @0
    @1
    @8
    @11
    @12
    wceq
    #
    @2
    @0
    @1
    @8
    @13
    @8
    @0
    @1
    @13
    @8
    @5
    cc
    wcel
    #
    @0
    cK
    cc
    wcel
    #
    @1
    cM
    cc
    wcel
    #
    @13
    @5
    zcn
    cK
    zcn
    cM
    zcn
    @14
    @15
    @16
    w3a
    @5
    cK
    cmul
    co
    cM
    cmul
    co
    @11
    @12
    @5
    cK
    cM
    mulass
    @5
    cK
    cM
    mul32
    eqtr3d
    syl3an
    3coml
    3expa
    3adantl3
    eqeq1d
    biimpd
    dvds1lem
end
