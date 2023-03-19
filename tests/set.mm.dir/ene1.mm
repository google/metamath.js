include "c1.mm"
include "ceu.mm"
include "1re.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "1lt2.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "2re.mm"
include "ere.mm"
include "lttri.mm"
include "mp2an.mm"
include "gtneii.mm"

theorem ene1



  assert |- _e =/= 1

  proof
    c1
    ceu
    1re
    c1
    c2
    clt
    wbr
    c2
    ceu
    clt
    wbr
    #
    c1
    ceu
    clt
    wbr
    1lt2
    @0
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    c1
    c2
    ceu
    1re
    2re
    ere
    lttri
    mp2an
    gtneii
end
