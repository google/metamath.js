include "c1.mm"
include "c8.mm"
include "cdiv.mm"
include "co.mm"
include "c4.mm"
include "c3.mm"
include "cmul.mm"
include "c6.mm"
include "ax-1cn.mm"
include "8re.mm"
include "recni.mm"
include "4cn.mm"
include "3cn.mm"
include "8pos.mm"
include "gt0ne0ii.mm"
include "3ne0.mm"
include "divmuldivi.mm"
include "mulcomi.mm"
include "c2.mm"
include "2cn.mm"
include "mul32i.mm"
include "4t2e8.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "mulassi.mm"
include "3t2e6.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "6re.mm"
include "6pos.mm"
include "4ne0.mm"
include "wa.mm"
include "divcan5.mm"
include "mp3an1.mm"
include "mp4an.mm"

theorem 8th4div3



  assert |- ( ( 1 / 8 ) x. ( 4 / 3 ) ) = ( 1 / 6 )

  proof
    c1
    c8
    cdiv
    co
    c4
    c3
    cdiv
    co
    cmul
    co
    #
    c4
    c1
    cmul
    co
    #
    c4
    c6
    cmul
    co
    #
    cdiv
    co
    #
    c1
    c6
    cdiv
    co
    #
    @0
    c1
    c4
    cmul
    co
    #
    c8
    c3
    cmul
    co
    #
    cdiv
    co
    @3
    c1
    c8
    c4
    c3
    ax-1cn
    c8
    8re
    recni
    4cn
    3cn
    c8
    8re
    8pos
    gt0ne0ii
    3ne0
    divmuldivi
    @5
    @1
    @6
    @2
    cdiv
    c1
    c4
    ax-1cn
    4cn
    mulcomi
    @6
    c4
    c3
    c2
    cmul
    co
    #
    cmul
    co
    #
    @2
    c4
    c3
    cmul
    co
    c2
    cmul
    co
    #
    @6
    @8
    c4
    c2
    cmul
    co
    #
    c3
    cmul
    co
    @9
    @6
    c4
    c2
    c3
    4cn
    2cn
    3cn
    mul32i
    @10
    c8
    c3
    cmul
    4t2e8
    oveq1i
    eqtr3i
    c4
    c3
    c2
    4cn
    3cn
    2cn
    mulassi
    eqtr3i
    @7
    c6
    c4
    cmul
    3t2e6
    oveq2i
    eqtri
    oveq12i
    eqtri
    c6
    cc
    wcel
    #
    c6
    cc0
    wne
    #
    c4
    cc
    wcel
    #
    c4
    cc0
    wne
    #
    @3
    @4
    wceq
    #
    c6
    6re
    recni
    c6
    6re
    6pos
    gt0ne0ii
    4cn
    4ne0
    c1
    cc
    wcel
    @11
    @12
    wa
    @13
    @14
    wa
    @15
    ax-1cn
    c1
    c6
    c4
    divcan5
    mp3an1
    mp4an
    eqtri
end
