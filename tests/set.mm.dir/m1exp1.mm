include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "wrex.mm"
include "2z.mm"
include "divides.mm"
include "mpan.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "zcn.mm"
include "2cnd.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "m1expeven.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "rexlimiva.mm"
include "syl6bi.mm"
include "impcom.mm"
include "simpl.mm"
include "2thd.mm"
include "wn.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "eqcom.mm"
include "ax-1cn.mm"
include "eqnegi.mm"
include "bitri.mm"
include "nemtbir.mm"
include "caddc.mm"
include "odd2np1.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "wne.mm"
include "neg1ne0.mm"
include "id.mm"
include "zmulcld.mm"
include "expp1zd.mm"
include "oveq1d.mm"
include "mulid2i.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "mtbiri.mm"
include "2falsed.mm"
include "pm2.61ian.mm"

theorem m1exp1
  let cN: class N
  let vn: setvar n


  assert |- ( N e. ZZ -> ( ( -u 1 ^ N ) = 1 <-> 2 || N ) )

  proof
    c2
    cN
    cdvds
    wbr
    #
    cN
    cz
    wcel
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    c1
    wceq
    #
    @0
    wb
    @0
    @1
    wa
    @4
    @0
    @1
    @0
    @4
    @1
    @0
    vn
    cv
    #
    c2
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @4
    c2
    cz
    wcel
    #
    @1
    @0
    @8
    wb
    2z
    vn
    c2
    cN
    divides
    mpan
    @7
    @4
    vn
    cz
    @7
    @5
    cz
    wcel
    #
    @3
    @2
    @6
    cexp
    co
    #
    c1
    @3
    @11
    wceq
    cN
    @6
    cN
    @6
    @2
    cexp
    oveq2
    eqcoms
    @10
    @11
    @2
    c2
    @5
    cmul
    co
    #
    cexp
    co
    #
    c1
    @10
    @6
    @12
    @2
    cexp
    @10
    @5
    c2
    @5
    zcn
    @10
    2cnd
    mulcomd
    oveq2d
    @5
    m1expeven
    #
    eqtrd
    sylan9eqr
    rexlimiva
    syl6bi
    impcom
    @0
    @1
    simpl
    2thd
    @0
    wn
    #
    @1
    wa
    #
    @4
    @0
    @16
    @4
    @2
    c1
    wceq
    #
    @17
    c1
    cc0
    ax-1ne0
    @17
    c1
    @2
    wceq
    c1
    cc0
    wceq
    @2
    c1
    eqcom
    c1
    ax-1cn
    eqnegi
    bitri
    nemtbir
    @16
    @3
    @2
    c1
    @1
    @15
    @3
    @2
    wceq
    #
    @1
    @15
    @12
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    @18
    vn
    cN
    odd2np1
    @20
    @18
    vn
    cz
    @20
    @10
    @3
    @2
    @19
    cexp
    co
    #
    @2
    @3
    @21
    wceq
    cN
    @19
    cN
    @19
    @2
    cexp
    oveq2
    eqcoms
    @10
    @21
    @13
    @2
    cmul
    co
    #
    @2
    @10
    @2
    @12
    @2
    cc
    wcel
    @10
    neg1cn
    a1i
    @2
    cc0
    wne
    @10
    neg1ne0
    a1i
    @10
    c2
    @5
    @9
    @10
    2z
    a1i
    @10
    id
    zmulcld
    expp1zd
    @10
    @22
    c1
    @2
    cmul
    co
    @2
    @10
    @13
    c1
    @2
    cmul
    @14
    oveq1d
    @2
    neg1cn
    mulid2i
    syl6eq
    eqtrd
    sylan9eqr
    rexlimiva
    syl6bi
    impcom
    eqeq1d
    mtbiri
    @15
    @1
    simpl
    2falsed
    pm2.61ian
end
