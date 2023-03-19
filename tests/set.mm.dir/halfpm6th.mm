include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c6.mm"
include "cmin.mm"
include "c3.mm"
include "wceq.mm"
include "caddc.mm"
include "cmul.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "2cn.mm"
include "3ne0.mm"
include "2ne0.mm"
include "divmuldivi.mm"
include "dividi.mm"
include "oveq1i.mm"
include "halfcn.mm"
include "mulid2i.mm"
include "eqtri.mm"
include "mulid1i.mm"
include "3t2e6.mm"
include "oveq12i.mm"
include "3eqtr3i.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "6cn.mm"
include "6re.mm"
include "6pos.mm"
include "gt0ne0ii.mm"
include "pm3.2i.mm"
include "divsubdir.mm"
include "mp3an.mm"
include "3m1e2.mm"
include "oveq2i.mm"
include "reccli.mm"
include "3eqtr2i.mm"
include "c4.mm"
include "divdiri.mm"
include "df-4.mm"
include "3eqtr4ri.mm"
include "2t2e4.mm"
include "divcli.mm"

theorem halfpm6th



  assert |- ( ( ( 1 / 2 ) - ( 1 / 6 ) ) = ( 1 / 3 ) /\ ( ( 1 / 2 ) + ( 1 / 6 ) ) = ( 2 / 3 ) )

  proof
    c1
    c2
    cdiv
    co
    #
    c1
    c6
    cdiv
    co
    #
    cmin
    co
    #
    c1
    c3
    cdiv
    co
    #
    wceq
    @0
    @1
    caddc
    co
    #
    c2
    c3
    cdiv
    co
    #
    wceq
    @2
    c3
    c6
    cdiv
    co
    #
    @1
    cmin
    co
    #
    c3
    c1
    cmin
    co
    #
    c6
    cdiv
    co
    #
    @3
    @0
    @6
    @1
    cmin
    c3
    c3
    cdiv
    co
    #
    @0
    cmul
    co
    #
    c3
    c1
    cmul
    co
    #
    c3
    c2
    cmul
    co
    #
    cdiv
    co
    @0
    @6
    c3
    c3
    c1
    c2
    3cn
    3cn
    ax-1cn
    2cn
    3ne0
    2ne0
    divmuldivi
    @11
    c1
    @0
    cmul
    co
    @0
    @10
    c1
    @0
    cmul
    c3
    3cn
    3ne0
    dividi
    oveq1i
    @0
    halfcn
    mulid2i
    eqtri
    @12
    c3
    @13
    c6
    cdiv
    c3
    3cn
    mulid1i
    3t2e6
    oveq12i
    3eqtr3i
    #
    oveq1i
    c3
    cc
    wcel
    c1
    cc
    wcel
    c6
    cc
    wcel
    #
    c6
    cc0
    wne
    #
    wa
    @9
    @7
    wceq
    3cn
    ax-1cn
    @15
    @16
    6cn
    c6
    6re
    6pos
    gt0ne0ii
    #
    pm3.2i
    c3
    c1
    c6
    divsubdir
    mp3an
    @9
    c2
    c6
    cdiv
    co
    c1
    c2
    cmul
    co
    #
    @13
    cdiv
    co
    #
    @3
    @8
    c2
    c6
    cdiv
    3m1e2
    oveq1i
    @18
    c2
    @13
    c6
    cdiv
    c2
    2cn
    mulid2i
    3t2e6
    oveq12i
    @3
    c2
    c2
    cdiv
    co
    #
    cmul
    co
    @3
    c1
    cmul
    co
    @19
    @3
    @20
    c1
    @3
    cmul
    c2
    2cn
    2ne0
    dividi
    #
    oveq2i
    c1
    c3
    c2
    c2
    ax-1cn
    3cn
    2cn
    2cn
    3ne0
    2ne0
    divmuldivi
    @3
    c3
    3cn
    3ne0
    reccli
    mulid1i
    3eqtr3i
    3eqtr2i
    3eqtr2i
    @4
    c4
    c6
    cdiv
    co
    #
    c2
    c2
    cmul
    co
    #
    @13
    cdiv
    co
    #
    @5
    c3
    c1
    caddc
    co
    #
    c6
    cdiv
    co
    @6
    @1
    caddc
    co
    @22
    @4
    c3
    c1
    c6
    3cn
    ax-1cn
    6cn
    @17
    divdiri
    c4
    @25
    c6
    cdiv
    df-4
    oveq1i
    @0
    @6
    @1
    caddc
    @14
    oveq1i
    3eqtr4ri
    @23
    c4
    @13
    c6
    cdiv
    2t2e4
    3t2e6
    oveq12i
    @5
    @20
    cmul
    co
    @5
    c1
    cmul
    co
    @24
    @5
    @20
    c1
    @5
    cmul
    @21
    oveq2i
    c2
    c3
    c2
    c2
    2cn
    3cn
    2cn
    2cn
    3ne0
    2ne0
    divmuldivi
    @5
    c2
    c3
    2cn
    3cn
    3ne0
    divcli
    mulid1i
    3eqtr3i
    3eqtr2i
    pm3.2i
end
