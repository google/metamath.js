include "c6.mm"
include "c4.mm"
include "cgcd.mm"
include "co.mm"
include "c2.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "6nn.mm"
include "nnzi.mm"
include "4z.mm"
include "gcdcom.mm"
include "mp2an.mm"
include "4cn.mm"
include "2cn.mm"
include "4p2e6.mm"
include "addcomli.mm"
include "oveq2i.mm"
include "2z.mm"
include "gcdadd.mm"
include "2p2e4.mm"
include "eqtri.mm"
include "cabs.mm"
include "cfv.mm"
include "gcdid.mm"
include "ax-mp.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "2re.mm"
include "0le2.mm"
include "absid.mm"
include "3eqtr3ri.mm"
include "3eqtr2i.mm"

theorem 6gcd4e2



  assert |- ( 6 gcd 4 ) = 2

  proof
    c6
    c4
    cgcd
    co
    #
    c4
    c6
    cgcd
    co
    #
    c4
    c2
    c4
    caddc
    co
    #
    cgcd
    co
    #
    c2
    c6
    cz
    wcel
    c4
    cz
    wcel
    #
    @0
    @1
    wceq
    c6
    6nn
    nnzi
    4z
    c6
    c4
    gcdcom
    mp2an
    @2
    c6
    c4
    cgcd
    c4
    c2
    c6
    4cn
    2cn
    4p2e6
    addcomli
    oveq2i
    c2
    c2
    cgcd
    co
    #
    c4
    c2
    cgcd
    co
    #
    c2
    @3
    @5
    c2
    c2
    c2
    caddc
    co
    #
    cgcd
    co
    #
    @6
    c2
    cz
    wcel
    #
    @9
    @5
    @8
    wceq
    2z
    2z
    c2
    c2
    gcdadd
    mp2an
    @8
    c2
    c4
    cgcd
    co
    #
    @6
    @7
    c4
    c2
    cgcd
    2p2e4
    oveq2i
    @9
    @4
    @10
    @6
    wceq
    2z
    4z
    c2
    c4
    gcdcom
    mp2an
    eqtri
    eqtri
    @5
    c2
    cabs
    cfv
    #
    c2
    @9
    @5
    @11
    wceq
    2z
    c2
    gcdid
    ax-mp
    c2
    cr
    wcel
    cc0
    c2
    cle
    wbr
    @11
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    eqtri
    @4
    @9
    @6
    @3
    wceq
    4z
    2z
    c4
    c2
    gcdadd
    mp2an
    3eqtr3ri
    3eqtr2i
end
