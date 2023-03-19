include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "c3.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wn.mm"
include "1z.mm"
include "cmul.mm"
include "2cn.mm"
include "mulid2i.mm"
include "2lt3.mm"
include "eqbrtri.mm"
include "cr.mm"
include "cc0.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "3re.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltmuldiv.mm"
include "mp3an.mm"
include "mpbi.mm"
include "c4.mm"
include "3lt4.mm"
include "2t2e4.mm"
include "breq2i.mm"
include "mpbir.mm"
include "1p1e2.mm"
include "ltdivmul.mm"
include "bitri.mm"
include "btwnnz.mm"

theorem 3halfnz



  assert |- -. ( 3 / 2 ) e. ZZ

  proof
    c1
    cz
    wcel
    c1
    c3
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @0
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @0
    cz
    wcel
    wn
    1z
    c1
    c2
    cmul
    co
    #
    c3
    clt
    wbr
    #
    @1
    @4
    c2
    c3
    clt
    c2
    2cn
    mulid2i
    2lt3
    eqbrtri
    c1
    cr
    wcel
    c3
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
    @5
    @1
    wb
    1re
    3re
    @7
    @8
    2re
    2pos
    pm3.2i
    #
    c1
    c3
    c2
    ltmuldiv
    mp3an
    mpbi
    @3
    c3
    c2
    c2
    cmul
    co
    #
    clt
    wbr
    #
    @12
    c3
    c4
    clt
    wbr
    3lt4
    @11
    c4
    c3
    clt
    2t2e4
    breq2i
    mpbir
    @3
    @0
    c2
    clt
    wbr
    #
    @12
    @2
    c2
    @0
    clt
    1p1e2
    breq2i
    @6
    @7
    @9
    @13
    @12
    wb
    3re
    2re
    @10
    c3
    c2
    c2
    ltdivmul
    mp3an
    bitri
    mpbir
    c1
    @0
    btwnnz
    mp3an
end
