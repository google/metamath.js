include "cxrs.mm"
include "cmgm.mm"
include "csgrp.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "xrsmgm.mm"
include "xrsnsgrp.mm"
include "neli.mm"
include "eldif.mm"
include "mpbir2an.mm"

theorem xrsmgmdifsgrp



  assert |- RR*s e. ( Mgm \ SGrp )

  proof
    cxrs
    cmgm
    csgrp
    cdif
    wcel
    cxrs
    cmgm
    wcel
    cxrs
    csgrp
    wcel
    wn
    xrsmgm
    cxrs
    csgrp
    xrsnsgrp
    neli
    cxrs
    cmgm
    csgrp
    eldif
    mpbir2an
end
