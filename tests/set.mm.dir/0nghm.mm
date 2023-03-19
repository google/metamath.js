include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cnghm.mm"
include "co.mm"
include "cnmo.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "eqid.mm"
include "nmo0.mm"
include "0re.mm"
include "syl6eqel.mm"
include "cghm.mm"
include "wb.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "0ghm.mm"
include "syl2an.mm"
include "isnghm2.mm"
include "mpd3an3.mm"
include "mpbird.mm"

theorem 0nghm
  let cS: class S
  let cT: class T
  let cV: class V
  let c.0: class .0.
  assume 0nghm.2: |- V = ( Base ` S )
  assume 0nghm.3: |- .0. = ( 0g ` T )


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp ) -> ( V X. { .0. } ) e. ( S NGHom T ) )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    wa
    #
    cV
    c.0
    csn
    cxp
    #
    cS
    cT
    cnghm
    co
    wcel
    #
    @3
    cS
    cT
    cnmo
    co
    #
    cfv
    #
    cr
    wcel
    #
    @2
    @6
    cc0
    cr
    cS
    cT
    @5
    cV
    c.0
    @5
    eqid
    #
    0nghm.2
    0nghm.3
    nmo0
    0re
    syl6eqel
    @0
    @1
    @3
    cS
    cT
    cghm
    co
    wcel
    #
    @4
    @7
    wb
    @0
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    @9
    @1
    cS
    ngpgrp
    cT
    ngpgrp
    cV
    cS
    cT
    c.0
    0nghm.3
    0nghm.2
    0ghm
    syl2an
    cS
    cT
    @3
    @5
    @8
    isnghm2
    mpd3an3
    mpbird
end
