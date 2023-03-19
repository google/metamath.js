include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ccmn.mm"
include "isabl.mm"
include "simprbi.mm"

theorem ablcmn
  let cG: class G


  assert |- ( G e. Abel -> G e. CMnd )

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
    simprbi
end
