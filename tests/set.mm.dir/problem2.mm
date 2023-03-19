include "c2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "c5.mm"
include "caddc.mm"
include "c4.mm"
include "c9.mm"
include "c3.mm"
include "2re.mm"
include "recni.mm"
include "10re.mm"
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

theorem problem2



  assert |- ( ( ( 2 x. ; 1 0 ) + 5 ) + ( ( 1 x. ; 1 0 ) + 4 ) ) = ( ( 3 x. ; 1 0 ) + 9 )

  proof
    c2
    c1
    cc0
    cdc
    #
    cmul
    co
    #
    c5
    caddc
    co
    c1
    @0
    cmul
    co
    #
    c4
    caddc
    co
    caddc
    co
    @1
    @2
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
    @0
    cmul
    co
    #
    c9
    caddc
    co
    c3
    @0
    cmul
    co
    #
    c9
    caddc
    co
    @1
    c5
    @2
    c4
    c2
    @0
    c2
    2re
    recni
    #
    @0
    10re
    recni
    #
    mulcli
    c5
    5re
    recni
    c1
    @0
    c1
    1re
    recni
    #
    @9
    mulcli
    c4
    4re
    recni
    add4i
    @3
    @6
    @4
    c9
    caddc
    @6
    @3
    c2
    c1
    @0
    @8
    @10
    @9
    adddiri
    eqcomi
    5p4e9
    oveq12i
    @6
    @7
    c9
    caddc
    @5
    c3
    @0
    cmul
    c3
    @5
    df-3
    eqcomi
    oveq1i
    oveq1i
    3eqtri
end
