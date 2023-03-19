include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "cv.mm"
include "id.mm"
include "znegcl.mm"
include "anim1i.mm"
include "adantl.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "mul2neg.mm"
include "syl2anr.mm"
include "adantlr.mm"
include "eqeq1d.mm"
include "biimprd.mm"
include "dvds1lem.mm"
include "mulneg12.mm"
include "impbid.mm"

theorem negdvdsb
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> -u M || N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    cdvds
    wbr
    cM
    cneg
    #
    cN
    cdvds
    wbr
    @2
    vx
    cM
    cN
    @3
    cN
    vx
    cv
    #
    cneg
    #
    @2
    id
    #
    @0
    @3
    cz
    wcel
    @1
    cM
    znegcl
    anim1i
    #
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    @2
    @4
    znegcl
    adantl
    #
    @2
    @8
    wa
    #
    @5
    @3
    cmul
    co
    #
    cN
    wceq
    @4
    cM
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
    @8
    @11
    @12
    wceq
    #
    @1
    @8
    @4
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    @13
    @0
    @4
    zcn
    #
    cM
    zcn
    #
    @4
    cM
    mul2neg
    syl2anr
    adantlr
    eqeq1d
    biimprd
    dvds1lem
    @2
    vx
    @3
    cN
    cM
    cN
    @5
    @7
    @6
    @9
    @10
    @5
    cM
    cmul
    co
    #
    cN
    wceq
    @4
    @3
    cmul
    co
    #
    cN
    wceq
    @10
    @18
    @19
    cN
    @0
    @8
    @18
    @19
    wceq
    #
    @1
    @8
    @14
    @15
    @20
    @0
    @16
    @17
    @4
    cM
    mulneg12
    syl2anr
    adantlr
    eqeq1d
    biimprd
    dvds1lem
    impbid
end
