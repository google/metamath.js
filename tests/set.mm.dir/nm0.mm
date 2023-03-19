include "cngp.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "eqid.mm"
include "cbs.mm"
include "wb.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "nmeq0.mm"
include "mpdan.mm"
include "mpbiri.mm"

theorem nm0
  let cG: class G
  let cN: class N
  let c.0: class .0.
  assume nm0.n: |- N = ( norm ` G )
  assume nm0.z: |- .0. = ( 0g ` G )


  assert |- ( G e. NrmGrp -> ( N ` .0. ) = 0 )

  proof
    cG
    cngp
    wcel
    #
    c.0
    cN
    cfv
    cc0
    wceq
    #
    c.0
    c.0
    wceq
    #
    c.0
    eqid
    @0
    c.0
    cG
    cbs
    cfv
    #
    wcel
    #
    @1
    @2
    wb
    @0
    cG
    cgrp
    wcel
    @4
    cG
    ngpgrp
    @3
    cG
    c.0
    @3
    eqid
    #
    nm0.z
    grpidcl
    syl
    c.0
    cG
    cN
    @3
    c.0
    @5
    nm0.n
    nm0.z
    nmeq0
    mpdan
    mpbiri
end
