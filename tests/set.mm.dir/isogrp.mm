include "cgrp.mm"
include "comnd.mm"
include "cogrp.mm"
include "df-ogrp.mm"
include "elin2.mm"

theorem isogrp
  let cG: class G


  assert |- ( G e. oGrp <-> ( G e. Grp /\ G e. oMnd ) )

  proof
    cG
    cgrp
    comnd
    cogrp
    df-ogrp
    elin2
end
