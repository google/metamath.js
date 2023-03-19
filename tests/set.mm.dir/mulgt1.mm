include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "cc0.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "adantr.mm"
include "w3a.mm"
include "ltmul2.mm"
include "biimpd.mm"
include "mp3an1.mm"
include "exp32.mm"
include "impcom.mm"
include "syld.mm"
include "impd.mm"
include "wceq.mm"
include "ax-1rid.mm"
include "breq1d.mm"
include "sylibd.mm"
include "jcad.mm"
include "remulcl.mm"
include "syldan.mm"
include "imp.mm"

theorem mulgt1
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 1 < A /\ 1 < B ) ) -> 1 < ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    c1
    cA
    clt
    wbr
    #
    c1
    cB
    clt
    wbr
    #
    wa
    #
    c1
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @5
    @3
    cA
    @6
    clt
    wbr
    #
    wa
    #
    @7
    @2
    @5
    @3
    @8
    @5
    @3
    wi
    @2
    @3
    @4
    simpl
    a1i
    @2
    @5
    cA
    c1
    cmul
    co
    #
    @6
    clt
    wbr
    #
    @8
    @2
    @3
    @4
    @11
    @2
    @3
    cc0
    cA
    clt
    wbr
    #
    @4
    @11
    wi
    #
    @0
    @3
    @12
    wi
    @1
    @0
    cc0
    c1
    clt
    wbr
    #
    @3
    @12
    0lt1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    #
    @0
    @14
    @3
    wa
    @12
    wi
    0re
    1re
    cc0
    c1
    cA
    lttr
    mp3an12
    mpani
    adantr
    @1
    @0
    @12
    @13
    wi
    @1
    @0
    @12
    @13
    @15
    @1
    @0
    @12
    wa
    #
    @13
    1re
    @15
    @1
    @16
    w3a
    @4
    @11
    c1
    cB
    cA
    ltmul2
    biimpd
    mp3an1
    exp32
    impcom
    syld
    impd
    @2
    @10
    cA
    @6
    clt
    @0
    @10
    cA
    wceq
    @1
    cA
    ax-1rid
    adantr
    breq1d
    sylibd
    jcad
    @0
    @1
    @6
    cr
    wcel
    #
    @9
    @7
    wi
    #
    cA
    cB
    remulcl
    @15
    @0
    @17
    @18
    1re
    c1
    cA
    @6
    lttr
    mp3an1
    syldan
    syld
    imp
end
