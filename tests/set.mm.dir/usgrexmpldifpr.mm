include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "wne.mm"
include "c3.mm"
include "w3a.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "0z.mm"
include "1z.mm"
include "pm3.2i.mm"
include "2z.mm"
include "ax-1ne0.mm"
include "necomi.mm"
include "2ne0.mm"
include "orci.mm"
include "prneimg.mm"
include "mp2.mm"
include "1ne2.mm"
include "olci.mm"
include "cn.mm"
include "3nn.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "3pm3.2i.mm"
include "2re.mm"
include "2lt3.mm"

theorem usgrexmpldifpr



  assert |- ( ( { 0 , 1 } =/= { 1 , 2 } /\ { 0 , 1 } =/= { 2 , 0 } /\ { 0 , 1 } =/= { 0 , 3 } ) /\ ( { 1 , 2 } =/= { 2 , 0 } /\ { 1 , 2 } =/= { 0 , 3 } /\ { 2 , 0 } =/= { 0 , 3 } ) )

  proof
    cc0
    c1
    cpr
    #
    c1
    c2
    cpr
    #
    wne
    #
    @0
    c2
    cc0
    cpr
    #
    wne
    #
    @0
    cc0
    c3
    cpr
    #
    wne
    #
    w3a
    @1
    @3
    wne
    #
    @1
    @5
    wne
    #
    @3
    @5
    wne
    #
    w3a
    @2
    @4
    @6
    cc0
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    wa
    #
    @11
    c2
    cz
    wcel
    #
    wa
    #
    wa
    cc0
    c1
    wne
    #
    cc0
    c2
    wne
    #
    wa
    #
    c1
    c1
    wne
    c1
    c2
    wne
    #
    wa
    #
    wo
    @2
    @12
    @14
    @10
    @11
    0z
    1z
    pm3.2i
    #
    @11
    @13
    1z
    2z
    pm3.2i
    #
    pm3.2i
    @17
    @19
    @15
    @16
    c1
    cc0
    ax-1ne0
    necomi
    c2
    cc0
    2ne0
    necomi
    pm3.2i
    orci
    cc0
    c1
    c1
    c2
    cz
    cz
    cz
    cz
    prneimg
    mp2
    @12
    @13
    @10
    wa
    #
    wa
    @16
    cc0
    cc0
    wne
    #
    wa
    #
    @18
    c1
    cc0
    wne
    #
    wa
    #
    wo
    @4
    @12
    @22
    @20
    @13
    @10
    2z
    0z
    pm3.2i
    #
    pm3.2i
    @26
    @24
    @18
    @25
    1ne2
    ax-1ne0
    pm3.2i
    #
    olci
    cc0
    c1
    c2
    cc0
    cz
    cz
    cz
    cz
    prneimg
    mp2
    @12
    @10
    c3
    cn
    wcel
    #
    wa
    #
    wa
    @23
    cc0
    c3
    wne
    wa
    #
    @25
    c1
    c3
    wne
    #
    wa
    #
    wo
    @6
    @12
    @30
    @20
    @10
    @29
    0z
    3nn
    pm3.2i
    #
    pm3.2i
    @33
    @31
    @25
    @32
    ax-1ne0
    c1
    c3
    1re
    1lt3
    ltneii
    pm3.2i
    #
    olci
    cc0
    c1
    cc0
    c3
    cz
    cz
    cz
    cn
    prneimg
    mp2
    3pm3.2i
    @7
    @8
    @9
    @14
    @22
    wa
    @26
    c2
    c2
    wne
    c2
    cc0
    wne
    #
    wa
    #
    wo
    @7
    @14
    @22
    @21
    @27
    pm3.2i
    @26
    @37
    @28
    orci
    c1
    c2
    c2
    cc0
    cz
    cz
    cz
    cz
    prneimg
    mp2
    @14
    @30
    wa
    @33
    @36
    c2
    c3
    wne
    #
    wa
    #
    wo
    @8
    @14
    @30
    @21
    @34
    pm3.2i
    @33
    @39
    @35
    orci
    c1
    c2
    cc0
    c3
    cz
    cz
    cz
    cn
    prneimg
    mp2
    @22
    @30
    wa
    @39
    @31
    wo
    @9
    @22
    @30
    @27
    @34
    pm3.2i
    @39
    @31
    @36
    @38
    2ne0
    c2
    c3
    2re
    2lt3
    ltneii
    pm3.2i
    orci
    c2
    cc0
    cc0
    c3
    cz
    cz
    cz
    cn
    prneimg
    mp2
    3pm3.2i
    pm3.2i
end
