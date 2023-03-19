include "cz.mm"
include "wcel.mm"
include "ci.mm"
include "c4.mm"
include "cmo.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "zre.mm"
include "4re.mm"
include "4pos.mm"
include "elrpii.mm"
include "modval.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "4z.mm"
include "cn.mm"
include "4nn.mm"
include "nndivre.mm"
include "flcld.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ax-icn.mm"
include "ine0.mm"
include "expsub.mm"
include "mpanl12.mm"
include "mpdan.mm"
include "c1.mm"
include "expmulz.mm"
include "i4.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "expclz.mm"
include "mp3an12.mm"
include "div1d.mm"

theorem iexpcyc
  let cK: class K


  assert |- ( K e. ZZ -> ( _i ^ ( K mod 4 ) ) = ( _i ^ K ) )

  proof
    cK
    cz
    wcel
    #
    ci
    cK
    c4
    cmo
    co
    #
    cexp
    co
    ci
    cK
    c4
    cK
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cexp
    co
    #
    ci
    cK
    cexp
    co
    #
    @0
    @1
    @5
    ci
    cexp
    @0
    cK
    cr
    wcel
    #
    c4
    crp
    wcel
    @1
    @5
    wceq
    cK
    zre
    #
    c4
    4re
    4pos
    elrpii
    cK
    c4
    modval
    sylancl
    oveq2d
    @0
    @6
    @7
    ci
    @4
    cexp
    co
    #
    cdiv
    co
    #
    @7
    @0
    @4
    cz
    wcel
    #
    @6
    @11
    wceq
    #
    @0
    c4
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @12
    4z
    @0
    @2
    @0
    @8
    c4
    cn
    wcel
    @2
    cr
    wcel
    @9
    4nn
    cK
    c4
    nndivre
    sylancl
    flcld
    #
    c4
    @3
    zmulcl
    sylancr
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @0
    @12
    wa
    @13
    ax-icn
    ine0
    ci
    cK
    @4
    expsub
    mpanl12
    mpdan
    @0
    @11
    @7
    c1
    cdiv
    co
    @7
    @0
    @10
    c1
    @7
    cdiv
    @0
    @10
    ci
    c4
    cexp
    co
    #
    @3
    cexp
    co
    #
    c1
    @0
    @14
    @15
    @10
    @20
    wceq
    #
    4z
    @16
    @17
    @18
    @14
    @15
    wa
    @21
    ax-icn
    ine0
    ci
    c4
    @3
    expmulz
    mpanl12
    sylancr
    @0
    @20
    c1
    @3
    cexp
    co
    #
    c1
    @19
    c1
    @3
    cexp
    i4
    oveq1i
    @0
    @15
    @22
    c1
    wceq
    @16
    @3
    1exp
    syl
    syl5eq
    eqtrd
    oveq2d
    @0
    @7
    @17
    @18
    @0
    @7
    cc
    wcel
    ax-icn
    ine0
    ci
    cK
    expclz
    mp3an12
    div1d
    eqtrd
    eqtrd
    eqtrd
end
