include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "grpidcl.mm"
include "grplid.mm"
include "mpdan.mm"
include "wb.mm"
include "grpinvid1.mm"
include "mpd3an23.mm"
include "mpbird.mm"

theorem grpinvid
  let cG: class G
  let cN: class N
  let c.0: class .0.
  assume grpinvid.u: |- .0. = ( 0g ` G )
  assume grpinvid.n: |- N = ( invg ` G )


  assert |- ( G e. Grp -> ( N ` .0. ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    c.0
    cN
    cfv
    c.0
    wceq
    #
    c.0
    c.0
    cG
    cplusg
    cfv
    #
    co
    c.0
    wceq
    #
    @0
    c.0
    cG
    cbs
    cfv
    #
    wcel
    #
    @3
    @4
    cG
    c.0
    @4
    eqid
    #
    grpinvid.u
    grpidcl
    #
    @4
    @2
    cG
    c.0
    c.0
    @6
    @2
    eqid
    #
    grpinvid.u
    grplid
    mpdan
    @0
    @5
    @5
    @1
    @3
    wb
    @7
    @7
    @4
    @2
    cG
    cN
    c.0
    c.0
    c.0
    @6
    @8
    grpinvid.u
    grpinvid.n
    grpinvid1
    mpd3an23
    mpbird
end
