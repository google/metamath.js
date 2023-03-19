include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "cv.mm"
include "id.mm"
include "znegcl.mm"
include "anim2i.mm"
include "adantl.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cc.mm"
include "zcn.mm"
include "mulneg1.mm"
include "negeq.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "syl2anr.mm"
include "adantlr.mm"
include "dvds1lem.mm"
include "negneg.mm"
include "sylan9eqr.mm"
include "sylan9eq.mm"
include "expr.mm"
include "3impa.mm"
include "syl3an.mm"
include "3coml.mm"
include "3expa.mm"
include "impbid.mm"

theorem dvdsnegb
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> M || -u N ) )

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
    cN
    cneg
    #
    cdvds
    wbr
    @2
    vx
    cM
    cN
    cM
    @3
    vx
    cv
    #
    cneg
    #
    @2
    id
    #
    @1
    @3
    cz
    wcel
    @0
    cN
    znegcl
    anim2i
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
    @0
    @8
    @4
    cM
    cmul
    co
    #
    cN
    wceq
    #
    @5
    cM
    cmul
    co
    #
    @3
    wceq
    #
    wi
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
    @14
    @0
    @4
    zcn
    #
    cM
    zcn
    #
    @15
    @16
    wa
    #
    @12
    @10
    cneg
    #
    wceq
    @11
    @13
    @4
    cM
    mulneg1
    #
    @11
    @20
    @3
    @12
    @10
    cN
    negeq
    eqeq2d
    syl5ibcom
    syl2anr
    adantlr
    dvds1lem
    @2
    vx
    cM
    @3
    cM
    cN
    @5
    @7
    @6
    @9
    @0
    @1
    @8
    @10
    @3
    wceq
    #
    @12
    cN
    wceq
    #
    wi
    #
    @8
    @0
    @1
    @24
    @8
    @15
    @0
    @16
    @1
    cN
    cc
    wcel
    #
    @24
    @17
    @18
    cN
    zcn
    @15
    @16
    @25
    @24
    @19
    @25
    @22
    @23
    @19
    @25
    @22
    wa
    @12
    @20
    cN
    @21
    @22
    @25
    @20
    @3
    cneg
    cN
    @10
    @3
    negeq
    cN
    negneg
    sylan9eqr
    sylan9eq
    expr
    3impa
    syl3an
    3coml
    3expa
    dvds1lem
    impbid
end
