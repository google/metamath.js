include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ccmn.mm"
include "isabl.mm"
include "simplbi.mm"

theorem ablgrp
  let cG: class G


  assert |- ( G e. Abel -> G e. Grp )

  proof
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    cG
    ccmn
    wcel
    cG
    isabl
    simplbi
end
