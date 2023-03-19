include "c3.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "clt.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "3cn.mm"
include "3nn0.mm"
include "expmul.mm"
include "mp3an.mm"
include "cr.mm"
include "cz.mm"
include "wbr.mm"
include "3re.mm"
include "nn0mulcli.mm"
include "nn0zi.mm"
include "nn0expcli.mm"
include "w3a.mm"
include "c1.mm"
include "1lt3.mm"
include "c2.mm"
include "sqvali.mm"
include "2z.mm"
include "3z.mm"
include "2lt3.mm"
include "ltexp2a.mm"
include "mpanr12.mm"
include "eqbrtrri.mm"

theorem expnass



  assert |- ( ( 3 ^ 3 ) ^ 3 ) < ( 3 ^ ( 3 ^ 3 ) )

  proof
    c3
    c3
    c3
    cmul
    co
    #
    cexp
    co
    #
    c3
    c3
    cexp
    co
    #
    c3
    cexp
    co
    #
    c3
    @2
    cexp
    co
    #
    clt
    c3
    cc
    wcel
    c3
    cn0
    wcel
    #
    @5
    @1
    @3
    wceq
    3cn
    3nn0
    3nn0
    c3
    c3
    c3
    expmul
    mp3an
    c3
    cr
    wcel
    #
    @0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @1
    @4
    clt
    wbr
    #
    3re
    @0
    c3
    c3
    3nn0
    3nn0
    nn0mulcli
    nn0zi
    @2
    c3
    c3
    3nn0
    3nn0
    nn0expcli
    nn0zi
    @6
    @7
    @8
    w3a
    c1
    c3
    clt
    wbr
    #
    @0
    @2
    clt
    wbr
    @9
    1lt3
    c3
    c2
    cexp
    co
    #
    @0
    @2
    clt
    c3
    3cn
    sqvali
    @6
    c2
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    @11
    @2
    clt
    wbr
    #
    3re
    2z
    3z
    @6
    @12
    @13
    w3a
    @10
    c2
    c3
    clt
    wbr
    @14
    1lt3
    2lt3
    c3
    c2
    c3
    ltexp2a
    mpanr12
    mp3an
    eqbrtrri
    c3
    @0
    @2
    ltexp2a
    mpanr12
    mp3an
    eqbrtrri
end
