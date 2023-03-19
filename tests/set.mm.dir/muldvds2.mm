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
include "3simpc.mm"
include "ancoms.mm"
include "3ad2antl1.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "mulass.mm"
include "syl3an.mm"
include "3coml.mm"
include "3expa.mm"
include "3adantl3.mm"
include "eqeq1d.mm"
include "biimprd.mm"
include "dvds1lem.mm"

theorem muldvds2
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K x. M ) || N -> M || N ) )

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
    cM
    cN
    vx
    cv
    #
    cK
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
    3simpc
    @0
    @1
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
    @0
    @9
    @5
    cK
    zmulcl
    ancoms
    3ad2antl1
    @3
    @8
    wa
    #
    @6
    cM
    cmul
    co
    #
    cN
    wceq
    @5
    @4
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
    @0
    cK
    cc
    wcel
    @1
    cM
    cc
    wcel
    @13
    @5
    zcn
    cK
    zcn
    cM
    zcn
    @5
    cK
    cM
    mulass
    syl3an
    3coml
    3expa
    3adantl3
    eqeq1d
    biimprd
    dvds1lem
end
