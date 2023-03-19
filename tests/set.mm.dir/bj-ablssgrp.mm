include "cabl.mm"
include "cgrp.mm"
include "ccmn.mm"
include "cin.mm"
include "df-abl.mm"
include "inss1.mm"
include "eqsstri.mm"

theorem bj-ablssgrp



  assert |- Abel C_ Grp

  proof
    cabl
    cgrp
    ccmn
    cin
    cgrp
    df-abl
    cgrp
    ccmn
    inss1
    eqsstri
end
