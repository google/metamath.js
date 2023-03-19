include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "syl.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "1cnd.mm"
include "2cnne0.mm"
include "a1i.mm"
include "divdir.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "halfge0.mm"
include "halflt1.mm"
include "pm3.2i.mm"
include "cr.mm"
include "wb.mm"
include "zob.mm"
include "biimpa.mm"
include "halfre.mm"
include "flbi2.mm"
include "sylancl.mm"
include "mpbiri.mm"

theorem zofldiv2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ ( ( N + 1 ) / 2 ) e. ZZ ) -> ( |_ ` ( N / 2 ) ) = ( ( N - 1 ) / 2 ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cz
    wcel
    #
    wa
    #
    cN
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @6
    @0
    @4
    @9
    wceq
    @1
    @0
    @3
    @8
    cfl
    @0
    @3
    @5
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @8
    @0
    cN
    @10
    c2
    cdiv
    @0
    cN
    cc
    wcel
    #
    cN
    @10
    wceq
    cN
    zcn
    @12
    @10
    cN
    cN
    npcan1
    eqcomd
    syl
    oveq1d
    @0
    @5
    cc
    wcel
    c1
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @11
    @8
    wceq
    @0
    @5
    cN
    peano2zm
    zcnd
    @0
    1cnd
    @13
    @0
    2cnne0
    a1i
    @5
    c1
    c2
    divdir
    syl3anc
    eqtrd
    fveq2d
    adantr
    @2
    @9
    @6
    wceq
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    c1
    clt
    wbr
    #
    wa
    #
    @15
    @16
    halfge0
    halflt1
    pm3.2i
    @2
    @6
    cz
    wcel
    #
    @7
    cr
    wcel
    @14
    @17
    wb
    @0
    @1
    @18
    cN
    zob
    biimpa
    halfre
    @7
    @6
    flbi2
    sylancl
    mpbiri
    eqtrd
end
