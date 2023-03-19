include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cmhm.mm"
include "co.mm"
include "cghm.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "0mhm.mm"
include "syl2an.mm"
include "ghmmhmb.mm"
include "eleqtrrd.mm"

theorem 0ghm
  let cB: class B
  let cM: class M
  let cN: class N
  let c.0: class .0.
  assume 0ghm.z: |- .0. = ( 0g ` N )
  assume 0ghm.b: |- B = ( Base ` M )


  assert |- ( ( M e. Grp /\ N e. Grp ) -> ( B X. { .0. } ) e. ( M GrpHom N ) )

  proof
    cM
    cgrp
    wcel
    #
    cN
    cgrp
    wcel
    #
    wa
    cB
    c.0
    csn
    cxp
    #
    cM
    cN
    cmhm
    co
    #
    cM
    cN
    cghm
    co
    @0
    cM
    cmnd
    wcel
    cN
    cmnd
    wcel
    @2
    @3
    wcel
    @1
    cM
    grpmnd
    cN
    grpmnd
    cB
    cM
    cN
    c.0
    0ghm.z
    0ghm.b
    0mhm
    syl2an
    cM
    cN
    ghmmhmb
    eleqtrrd
end
