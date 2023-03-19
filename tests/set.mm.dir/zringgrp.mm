include "zring.mm"
include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "zringring.mm"
include "ringgrp.mm"
include "ax-mp.mm"

theorem zringgrp



  assert |- ZZring e. Grp

  proof
    zring
    crg
    wcel
    zring
    cgrp
    wcel
    zringring
    zring
    ringgrp
    ax-mp
end
