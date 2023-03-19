include "cgrp.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "grpidcl.mm"
include "ne0i.mm"
include "syl.mm"

theorem grpbn0
  let cB: class B
  let cG: class G
  assume grpbn0.b: |- B = ( Base ` G )


  assert |- ( G e. Grp -> B =/= (/) )

  proof
    cG
    cgrp
    wcel
    cG
    c0g
    cfv
    #
    cB
    wcel
    cB
    c0
    wne
    cB
    cG
    @0
    grpbn0.b
    @0
    eqid
    grpidcl
    cB
    @0
    ne0i
    syl
end
