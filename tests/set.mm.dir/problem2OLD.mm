include "c2.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "c5.mm"
include "caddc.mm"
include "c1.mm"
include "c4.mm"
include "c9.mm"
include "c3.mm"
include "2re.mm"
include "recni.mm"
include "10reOLD.mm"
include "mulcli.mm"
include "5re.mm"
include "1re.mm"
include "4re.mm"
include "add4i.mm"
include "adddiri.mm"
include "eqcomi.mm"
include "5p4e9.mm"
include "oveq12i.mm"
include "df-3.mm"
include "oveq1i.mm"
include "3eqtri.mm"

theorem problem2OLD



  assert |- ( ( ( 2 x. 10 ) + 5 ) + ( ( 1 x. 10 ) + 4 ) ) = ( ( 3 x. 10 ) + 9 )

  proof
    c2
    c10
    cmul
    co
    #
    c5
    caddc
    co
    c1
    c10
    cmul
    co
    #
    c4
    caddc
    co
    caddc
    co
    @0
    @1
    caddc
    co
    #
    c5
    c4
    caddc
    co
    #
    caddc
    co
    c2
    c1
    caddc
    co
    #
    c10
    cmul
    co
    #
    c9
    caddc
    co
    c3
    c10
    cmul
    co
    #
    c9
    caddc
    co
    @0
    c5
    @1
    c4
    c2
    c10
    c2
    2re
    recni
    #
    c10
    10reOLD
    recni
    #
    mulcli
    c5
    5re
    recni
    c1
    c10
    c1
    1re
    recni
    #
    @8
    mulcli
    c4
    4re
    recni
    add4i
    @2
    @5
    @3
    c9
    caddc
    @5
    @2
    c2
    c1
    c10
    @7
    @9
    @8
    adddiri
    eqcomi
    5p4e9
    oveq12i
    @5
    @6
    c9
    caddc
    @4
    c3
    c10
    cmul
    c3
    @4
    df-3
    eqcomi
    oveq1i
    oveq1i
    3eqtri
end
