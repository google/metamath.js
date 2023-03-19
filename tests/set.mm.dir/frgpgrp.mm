include "wcel.mm"
include "cgrp.mm"
include "c0.mm"
include "cefg.mm"
include "cfv.mm"
include "cec.mm"
include "c0g.mm"
include "wceq.mm"
include "eqid.mm"
include "frgp0.mm"
include "simpld.mm"

theorem frgpgrp
  let cG: class G
  let cI: class I
  let cV: class V
  assume frgpgrp.g: |- G = ( freeGrp ` I )


  assert |- ( I e. V -> G e. Grp )

  proof
    cI
    cV
    wcel
    cG
    cgrp
    wcel
    c0
    cI
    cefg
    cfv
    #
    cec
    cG
    c0g
    cfv
    wceq
    @0
    cG
    cI
    cV
    frgpgrp.g
    @0
    eqid
    frgp0
    simpld
end
