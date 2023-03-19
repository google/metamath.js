include "cgrp.mm"
include "ccmn.mm"
include "cabl.mm"
include "df-abl.mm"
include "elin2.mm"

theorem isabl
  let cG: class G


  assert |- ( G e. Abel <-> ( G e. Grp /\ G e. CMnd ) )

  proof
    cG
    cgrp
    ccmn
    cabl
    df-abl
    elin2
end
