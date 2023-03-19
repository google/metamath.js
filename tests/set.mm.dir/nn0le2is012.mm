include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "w3o.mm"
include "clt.mm"
include "wo.mm"
include "nn0re.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "leloed.mm"
include "wi.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "2z.mm"
include "zltlem1.mm"
include "sylancl.mm"
include "2m1e1.mm"
include "breq2d.mm"
include "bitrd.mm"
include "1red.mm"
include "nn0lt10b.mm"
include "3mix1.mm"
include "syl6bi.mm"
include "com12.mm"
include "3mix2.mm"
include "a1d.mm"
include "jaoi.mm"
include "sylbid.mm"
include "3mix3.mm"
include "imp.mm"

theorem nn0le2is012
  let cN: class N


  assert |- ( ( N e. NN0 /\ N <_ 2 ) -> ( N = 0 \/ N = 1 \/ N = 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    cle
    wbr
    #
    cN
    cc0
    wceq
    #
    cN
    c1
    wceq
    #
    cN
    c2
    wceq
    #
    w3o
    #
    @0
    @1
    cN
    c2
    clt
    wbr
    #
    @4
    wo
    #
    @5
    @0
    cN
    c2
    cN
    nn0re
    #
    c2
    cr
    wcel
    @0
    2re
    a1i
    leloed
    @7
    @0
    @5
    @6
    @0
    @5
    wi
    #
    @4
    @0
    @6
    @5
    @0
    @6
    cN
    c1
    cle
    wbr
    #
    @5
    @0
    @6
    cN
    c2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @10
    @0
    cN
    cz
    wcel
    c2
    cz
    wcel
    @6
    @12
    wb
    cN
    nn0z
    2z
    cN
    c2
    zltlem1
    sylancl
    @0
    @11
    c1
    cN
    cle
    @11
    c1
    wceq
    @0
    2m1e1
    a1i
    breq2d
    bitrd
    @0
    @10
    cN
    c1
    clt
    wbr
    #
    @3
    wo
    #
    @5
    @0
    cN
    c1
    @8
    @0
    1red
    leloed
    @14
    @0
    @5
    @13
    @9
    @3
    @0
    @13
    @5
    @0
    @13
    @2
    @5
    cN
    nn0lt10b
    @2
    @3
    @4
    3mix1
    syl6bi
    com12
    @3
    @5
    @0
    @3
    @2
    @4
    3mix2
    a1d
    jaoi
    com12
    sylbid
    sylbid
    com12
    @4
    @5
    @0
    @4
    @2
    @3
    3mix3
    a1d
    jaoi
    com12
    sylbid
    imp
end
