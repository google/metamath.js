include "cz.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "cv.mm"
include "3simpc.mm"
include "wa.mm"
include "zmulcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "jca.mm"
include "3comr.mm"
include "simpr.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "mulass.mm"
include "syl3an.mm"
include "3com13.mm"
include "3expa.mm"
include "3adantl3.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "ex.mm"
include "dvds1lem.mm"
include "3coml.mm"

theorem dvdsmulc
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) -> ( M || N -> ( M x. K ) || ( N x. K ) ) )

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
    cM
    cN
    cdvds
    wbr
    cM
    cK
    cmul
    co
    #
    cN
    cK
    cmul
    co
    #
    cdvds
    wbr
    wi
    @0
    @1
    @2
    w3a
    #
    vx
    cM
    cN
    @3
    @4
    vx
    cv
    #
    @0
    @1
    @2
    3simpc
    @1
    @2
    @0
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    wa
    @1
    @2
    @0
    w3a
    @7
    @8
    @1
    @0
    @7
    @2
    cM
    cK
    zmulcl
    3adant2
    @2
    @0
    @8
    @1
    cN
    cK
    zmulcl
    3adant1
    jca
    3comr
    @5
    @6
    cz
    wcel
    #
    simpr
    @5
    @9
    wa
    #
    @6
    cM
    cmul
    co
    #
    cN
    wceq
    #
    @6
    @3
    cmul
    co
    #
    @4
    wceq
    @10
    @12
    @13
    @11
    cK
    cmul
    co
    #
    @4
    @0
    @1
    @9
    @14
    @13
    wceq
    #
    @2
    @0
    @1
    @9
    @15
    @9
    @1
    @0
    @15
    @9
    @6
    cc
    wcel
    @1
    cM
    cc
    wcel
    @0
    cK
    cc
    wcel
    @15
    @6
    zcn
    cM
    zcn
    cK
    zcn
    @6
    cM
    cK
    mulass
    syl3an
    3com13
    3expa
    3adantl3
    @11
    cN
    cK
    cmul
    oveq1
    sylan9req
    ex
    dvds1lem
    3coml
end
