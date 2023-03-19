include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "clt.mm"
include "flodddiv4lt.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "zre.mm"
include "4re.mm"
include "a1i.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "adantr.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltmul1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wceq.mm"
include "zcn.mm"
include "halfcld.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divcan1d.mm"
include "cc.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "2t2e4.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "breqtrrd.mm"

theorem flodddiv4t2lthalf
  let cN: class N


  assert |- ( ( N e. ZZ /\ -. 2 || N ) -> ( ( |_ ` ( N / 4 ) ) x. 2 ) < ( N / 2 ) )

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
    wa
    #
    cN
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cmul
    co
    #
    @3
    c2
    cmul
    co
    #
    cN
    c2
    cdiv
    co
    #
    clt
    @2
    @4
    @3
    clt
    wbr
    #
    @5
    @6
    clt
    wbr
    #
    cN
    flodddiv4lt
    @2
    @4
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @8
    @9
    wb
    @0
    @10
    @1
    @0
    @4
    @0
    @3
    @0
    cN
    c4
    cN
    zre
    c4
    cr
    wcel
    @0
    4re
    a1i
    c4
    cc0
    wne
    @0
    4ne0
    a1i
    redivcld
    #
    flcld
    zred
    adantr
    @0
    @11
    @1
    @15
    adantr
    @14
    @2
    @12
    @13
    2re
    2pos
    pm3.2i
    a1i
    @4
    @3
    c2
    ltmul1
    syl3anc
    mpbid
    @0
    @7
    @6
    wceq
    @1
    @0
    @7
    c2
    cdiv
    co
    #
    c2
    cmul
    co
    @7
    @6
    @0
    @7
    c2
    @0
    cN
    cN
    zcn
    #
    halfcld
    @0
    2cnd
    c2
    cc0
    wne
    #
    @0
    2ne0
    a1i
    divcan1d
    @0
    @16
    @3
    c2
    cmul
    @0
    @16
    cN
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @3
    @0
    cN
    cc
    wcel
    c2
    cc
    wcel
    @18
    wa
    #
    @21
    @16
    @20
    wceq
    @17
    @21
    @0
    2cnne0
    a1i
    #
    @22
    cN
    c2
    c2
    divdiv1
    syl3anc
    @0
    @19
    c4
    cN
    cdiv
    @19
    c4
    wceq
    @0
    2t2e4
    a1i
    oveq2d
    eqtrd
    oveq1d
    eqtr3d
    adantr
    breqtrrd
end
