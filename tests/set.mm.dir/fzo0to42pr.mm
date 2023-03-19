include "cc0.mm"
include "c4.mm"
include "cfzo.mm"
include "co.mm"
include "c2.mm"
include "cun.mm"
include "c1.mm"
include "cpr.mm"
include "c3.mm"
include "cfz.mm"
include "wcel.mm"
include "wceq.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "2nn0.mm"
include "4nn0.mm"
include "2re.mm"
include "4re.mm"
include "2lt4.mm"
include "ltleii.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "fzosplit.mm"
include "ax-mp.mm"
include "fzo0to2pr.mm"
include "cmin.mm"
include "caddc.mm"
include "cz.mm"
include "4z.mm"
include "fzoval.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "df-4.mm"
include "addcomi.mm"
include "eqtri.mm"
include "eqcomi.mm"
include "subaddrii.mm"
include "df-3.mm"
include "oveq2i.mm"
include "2z.mm"
include "fzpr.mm"
include "preq2i.mm"
include "3eqtri.mm"
include "uneq12i.mm"

theorem fzo0to42pr



  assert |- ( 0 ..^ 4 ) = ( { 0 , 1 } u. { 2 , 3 } )

  proof
    cc0
    c4
    cfzo
    co
    #
    cc0
    c2
    cfzo
    co
    #
    c2
    c4
    cfzo
    co
    #
    cun
    #
    cc0
    c1
    cpr
    #
    c2
    c3
    cpr
    #
    cun
    c2
    cc0
    c4
    cfz
    co
    wcel
    #
    @0
    @3
    wceq
    @6
    c2
    cn0
    wcel
    c4
    cn0
    wcel
    c2
    c4
    cle
    wbr
    2nn0
    4nn0
    c2
    c4
    2re
    4re
    2lt4
    ltleii
    c2
    c4
    elfz2nn0
    mpbir3an
    cc0
    c4
    c2
    fzosplit
    ax-mp
    @1
    @4
    @2
    @5
    fzo0to2pr
    @2
    c2
    c4
    c1
    cmin
    co
    #
    cfz
    co
    #
    c2
    c2
    c1
    caddc
    co
    #
    cpr
    #
    @5
    c4
    cz
    wcel
    @2
    @8
    wceq
    4z
    c2
    c4
    fzoval
    ax-mp
    @8
    c2
    @9
    cfz
    co
    #
    @10
    @7
    @9
    c2
    cfz
    @7
    c3
    @9
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    c4
    c1
    c3
    caddc
    co
    #
    c4
    c3
    c1
    caddc
    co
    @12
    df-4
    c3
    c1
    3cn
    ax-1cn
    addcomi
    eqtri
    eqcomi
    subaddrii
    df-3
    eqtri
    oveq2i
    c2
    cz
    wcel
    @11
    @10
    wceq
    2z
    c2
    fzpr
    ax-mp
    eqtri
    @9
    c3
    c2
    c3
    @9
    df-3
    eqcomi
    preq2i
    3eqtri
    uneq12i
    eqtri
end
