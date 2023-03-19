include "c6.mm"
include "cneg.mm"
include "c9.mm"
include "cgcd.mm"
include "co.mm"
include "c3.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "6nn.mm"
include "nnzi.mm"
include "9nn.mm"
include "neggcd.mm"
include "mp2an.mm"
include "caddc.mm"
include "6cn.mm"
include "3cn.mm"
include "6p3e9.mm"
include "addcomli.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "3z.mm"
include "gcdcom.mm"
include "3p3e6.mm"
include "eqtri.mm"
include "gcdadd.mm"
include "cabs.mm"
include "cfv.mm"
include "gcdid.mm"
include "ax-mp.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "3re.mm"
include "0re.mm"
include "3pos.mm"
include "ltleii.mm"
include "absid.mm"
include "3eqtr3i.mm"

theorem ex-gcd



  assert |- ( -u 6 gcd 9 ) = 3

  proof
    c6
    cneg
    c9
    cgcd
    co
    #
    c6
    c9
    cgcd
    co
    #
    c3
    c6
    cz
    wcel
    #
    c9
    cz
    wcel
    @0
    @1
    wceq
    c6
    6nn
    nnzi
    #
    c9
    9nn
    nnzi
    c6
    c9
    neggcd
    mp2an
    @1
    c6
    c3
    c6
    caddc
    co
    #
    cgcd
    co
    #
    c3
    c9
    @4
    c6
    cgcd
    @4
    c9
    c6
    c3
    c9
    6cn
    3cn
    6p3e9
    addcomli
    eqcomi
    oveq2i
    c6
    c3
    cgcd
    co
    #
    c3
    c3
    c3
    caddc
    co
    #
    cgcd
    co
    #
    @5
    c3
    @6
    c3
    c6
    cgcd
    co
    #
    @8
    @2
    c3
    cz
    wcel
    #
    @6
    @9
    wceq
    @3
    3z
    c6
    c3
    gcdcom
    mp2an
    c6
    @7
    c3
    cgcd
    @7
    c6
    3p3e6
    eqcomi
    oveq2i
    eqtri
    @2
    @10
    @6
    @5
    wceq
    @3
    3z
    c6
    c3
    gcdadd
    mp2an
    c3
    c3
    cgcd
    co
    #
    c3
    cabs
    cfv
    #
    @8
    c3
    @10
    @11
    @12
    wceq
    3z
    c3
    gcdid
    ax-mp
    @10
    @10
    @11
    @8
    wceq
    3z
    3z
    c3
    c3
    gcdadd
    mp2an
    c3
    cr
    wcel
    cc0
    c3
    cle
    wbr
    @12
    c3
    wceq
    3re
    cc0
    c3
    0re
    3re
    3pos
    ltleii
    c3
    absid
    mp2an
    3eqtr3i
    3eqtr3i
    eqtri
    eqtri
end
