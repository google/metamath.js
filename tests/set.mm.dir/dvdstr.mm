include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "3simpa.mm"
include "3simpc.mm"
include "3simpb.mm"
include "wa.mm"
include "zmulcl.mm"
include "adantl.mm"
include "wceq.mm"
include "oveq2.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq2.mm"
include "mpbid.mm"
include "cc.mm"
include "zcn.mm"
include "mulass.mm"
include "mul12.mm"
include "eqtrd.mm"
include "syl3an.mm"
include "3comr.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "dvds2lem.mm"

theorem dvdstr
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K || M /\ M || N ) -> K || N ) )

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
    cM
    cN
    cK
    cN
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    @0
    @1
    @2
    3simpa
    @0
    @1
    @2
    3simpc
    @0
    @1
    @2
    3simpb
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    wa
    #
    @6
    cz
    wcel
    @3
    @4
    @5
    zmulcl
    adantl
    @4
    cK
    cmul
    co
    #
    cM
    wceq
    #
    @5
    cM
    cmul
    co
    #
    cN
    wceq
    #
    wa
    #
    @6
    cK
    cmul
    co
    #
    cN
    wceq
    @3
    @9
    wa
    #
    @5
    @10
    cmul
    co
    #
    cN
    wceq
    #
    @14
    @17
    @12
    wceq
    #
    @18
    @11
    @19
    @13
    @10
    cM
    @5
    cmul
    oveq2
    adantr
    @13
    @19
    @18
    wb
    @11
    @12
    cN
    @17
    eqeq2
    adantl
    mpbid
    @16
    @15
    @17
    cN
    @0
    @1
    @9
    @15
    @17
    wceq
    #
    @2
    @0
    @7
    @8
    @20
    @7
    @8
    @0
    @20
    @7
    @4
    cc
    wcel
    #
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
    @20
    @4
    zcn
    @5
    zcn
    cK
    zcn
    @21
    @22
    @23
    w3a
    @15
    @4
    @5
    cK
    cmul
    co
    cmul
    co
    @17
    @4
    @5
    cK
    mulass
    @4
    @5
    cK
    mul12
    eqtrd
    syl3an
    3comr
    3expb
    3ad2antl1
    eqeq1d
    syl5ibr
    dvds2lem
end
