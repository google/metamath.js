include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "odd2np1.mm"
include "wa.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "neg1ne0.mm"
include "2z.mm"
include "id.mm"
include "zmulcld.mm"
include "expp1zd.mm"
include "m1expeven.mm"
include "oveq1d.mm"
include "mulid2i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "adantl.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp.mm"

theorem m1expo
  let cN: class N
  let vn: setvar n


  assert |- ( ( N e. ZZ /\ -. 2 || N ) -> ( -u 1 ^ N ) = -u 1 )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    @2
    wceq
    #
    @0
    @1
    c2
    vn
    cv
    #
    cmul
    co
    #
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
    @4
    vn
    cN
    odd2np1
    @0
    @8
    @4
    vn
    cz
    @0
    @5
    cz
    wcel
    #
    wa
    #
    @8
    @4
    @8
    @10
    @3
    @2
    @7
    cexp
    co
    #
    @2
    @3
    @11
    wceq
    cN
    @7
    cN
    @7
    @2
    cexp
    oveq2
    eqcoms
    @9
    @11
    @2
    wceq
    @0
    @9
    @11
    @2
    @6
    cexp
    co
    #
    @2
    cmul
    co
    #
    @2
    @9
    @2
    @6
    @2
    cc
    wcel
    @9
    neg1cn
    a1i
    @2
    cc0
    wne
    @9
    neg1ne0
    a1i
    @9
    c2
    @5
    c2
    cz
    wcel
    @9
    2z
    a1i
    @9
    id
    zmulcld
    expp1zd
    @9
    @13
    c1
    @2
    cmul
    co
    @2
    @9
    @12
    c1
    @2
    cmul
    @5
    m1expeven
    oveq1d
    @2
    neg1cn
    mulid2i
    syl6eq
    eqtrd
    adantl
    sylan9eqr
    ex
    rexlimdva
    sylbid
    imp
end
