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
include "zmulcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "jca.mm"
include "simpr.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "mul12.mm"
include "syl3an.mm"
include "3coml.mm"
include "3expa.mm"
include "3adantl3.mm"
include "oveq2.mm"
include "sylan9eq.mm"
include "ex.mm"
include "dvds1lem.mm"

theorem dvdscmul
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) -> ( M || N -> ( K x. M ) || ( K x. N ) ) )

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
    cK
    cM
    cmul
    co
    #
    cK
    cN
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
    @5
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @0
    @1
    @7
    @2
    cK
    cM
    zmulcl
    3adant3
    @0
    @2
    @8
    @1
    cK
    cN
    zmulcl
    3adant2
    jca
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
    cK
    @11
    cmul
    co
    #
    @4
    @0
    @1
    @9
    @13
    @14
    wceq
    #
    @2
    @0
    @1
    @9
    @15
    @9
    @0
    @1
    @15
    @9
    @6
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
    @15
    @6
    zcn
    cK
    zcn
    cM
    zcn
    @6
    cK
    cM
    mul12
    syl3an
    3coml
    3expa
    3adantl3
    @11
    cN
    cK
    cmul
    oveq2
    sylan9eq
    ex
    dvds1lem
    3coml
end
