include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "3simpa.mm"
include "3simpb.mm"
include "wa.mm"
include "zsubcl.mm"
include "anim2i.mm"
include "3impb.mm"
include "adantl.mm"
include "cmul.mm"
include "wceq.mm"
include "wi.mm"
include "cc.mm"
include "zcn.mm"
include "subdir.mm"
include "syl3an.mm"
include "3comr.mm"
include "3expb.mm"
include "oveq12.mm"
include "sylan9eq.mm"
include "ex.mm"
include "3ad2antl1.mm"
include "dvds2lem.mm"

theorem dvds2sub
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K || M /\ K || N ) -> K || ( M - N ) ) )

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
    vy
    cK
    cM
    cK
    cN
    cK
    cM
    cN
    cmin
    co
    #
    vx
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    @0
    @1
    @2
    3simpa
    @0
    @1
    @2
    3simpb
    @0
    @1
    @2
    @0
    @4
    cz
    wcel
    #
    wa
    @1
    @2
    wa
    @8
    @0
    cM
    cN
    zsubcl
    anim2i
    3impb
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wa
    #
    @7
    cz
    wcel
    @3
    @5
    @6
    zsubcl
    adantl
    @0
    @1
    @11
    @5
    cK
    cmul
    co
    #
    cM
    wceq
    @6
    cK
    cmul
    co
    #
    cN
    wceq
    wa
    #
    @7
    cK
    cmul
    co
    #
    @4
    wceq
    #
    wi
    @2
    @0
    @11
    wa
    #
    @14
    @16
    @17
    @14
    @15
    @12
    @13
    cmin
    co
    #
    @4
    @0
    @9
    @10
    @15
    @18
    wceq
    #
    @9
    @10
    @0
    @19
    @9
    @5
    cc
    wcel
    @10
    @6
    cc
    wcel
    @0
    cK
    cc
    wcel
    @19
    @5
    zcn
    @6
    zcn
    cK
    zcn
    @5
    @6
    cK
    subdir
    syl3an
    3comr
    3expb
    @12
    cM
    @13
    cN
    cmin
    oveq12
    sylan9eq
    ex
    3ad2antl1
    dvds2lem
end
