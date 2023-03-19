include "cabl.mm"
include "cgrp.mm"
include "ccmn.mm"
include "cin.mm"
include "df-abl.mm"
include "inss2.mm"
include "eqsstri.mm"

theorem bj-ablsscmn



  assert |- Abel C_ CMnd

  proof
    cabl
    cgrp
    ccmn
    cin
    ccmn
    df-abl
    cgrp
    ccmn
    inss2
    eqsstri
end
