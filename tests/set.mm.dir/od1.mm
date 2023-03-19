include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "cn.mm"
include "cmg.mm"
include "eqid.mm"
include "grpidcl.mm"
include "1nn.mm"
include "a1i.mm"
include "mulg1.mm"
include "syl.mm"
include "odlem2.mm"
include "syl3anc.mm"
include "elfz1eq.mm"

theorem od1
  let cG: class G
  let cO: class O
  let c.0: class .0.
  assume od1.1: |- O = ( od ` G )
  assume od1.2: |- .0. = ( 0g ` G )


  assert |- ( G e. Grp -> ( O ` .0. ) = 1 )

  proof
    cG
    cgrp
    wcel
    #
    c.0
    cO
    cfv
    #
    c1
    c1
    cfz
    co
    wcel
    #
    @1
    c1
    wceq
    @0
    c.0
    cG
    cbs
    cfv
    #
    wcel
    #
    c1
    cn
    wcel
    #
    c1
    c.0
    cG
    cmg
    cfv
    #
    co
    c.0
    wceq
    #
    @2
    @3
    cG
    c.0
    @3
    eqid
    #
    od1.2
    grpidcl
    #
    @5
    @0
    1nn
    a1i
    @0
    @4
    @7
    @9
    @3
    @6
    cG
    c.0
    @8
    @6
    eqid
    #
    mulg1
    syl
    c.0
    @6
    cG
    c1
    cO
    @3
    c.0
    @8
    od1.1
    @10
    od1.2
    odlem2
    syl3anc
    @1
    c1
    elfz1eq
    syl
end
