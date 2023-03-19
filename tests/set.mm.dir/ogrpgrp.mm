include "cogrp.mm"
include "wcel.mm"
include "cgrp.mm"
include "comnd.mm"
include "isogrp.mm"
include "simplbi.mm"

theorem ogrpgrp
  let cG: class G


  assert |- ( G e. oGrp -> G e. Grp )

  proof
    cG
    cogrp
    wcel
    cG
    cgrp
    wcel
    cG
    comnd
    wcel
    cG
    isogrp
    simplbi
end
