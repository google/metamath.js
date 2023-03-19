include "codd.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "oddz.mm"
include "zcnd.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "peano2cnm.mm"
include "1cnd.mm"
include "2cnne0.mm"
include "a1i.mm"
include "divdir.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "syl.mm"
include "fveq2d.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "halfge0.mm"
include "halflt1.mm"
include "pm3.2i.mm"
include "cz.mm"
include "cr.mm"
include "wb.mm"
include "oddm1div2z.mm"
include "halfre.mm"
include "flbi2.mm"
include "sylancl.mm"
include "mpbiri.mm"

theorem zofldiv2ALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. Odd -> ( |_ ` ( N / 2 ) ) = ( ( N - 1 ) / 2 ) )

  proof
    cN
    codd
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cfl
    cfv
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
    @3
    @0
    @1
    @5
    cfl
    @0
    cN
    cc
    wcel
    #
    @1
    @5
    wceq
    @0
    cN
    cN
    oddz
    zcnd
    @7
    @1
    @2
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @5
    @7
    cN
    @8
    c2
    cdiv
    @7
    @8
    cN
    cN
    npcan1
    eqcomd
    oveq1d
    @7
    @2
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
    @9
    @5
    wceq
    cN
    peano2cnm
    @7
    1cnd
    @10
    @7
    2cnne0
    a1i
    @2
    c1
    c2
    divdir
    syl3anc
    eqtrd
    syl
    fveq2d
    @0
    @6
    @3
    wceq
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    c1
    clt
    wbr
    #
    wa
    #
    @12
    @13
    halfge0
    halflt1
    pm3.2i
    @0
    @3
    cz
    wcel
    @4
    cr
    wcel
    @11
    @14
    wb
    cN
    oddm1div2z
    halfre
    @4
    @3
    flbi2
    sylancl
    mpbiri
    eqtrd
end
