include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cgi.mm"
include "cfv.mm"
include "wceq.mm"
include "0vfval.mm"
include "oveq1d.mm"
include "adantr.mm"
include "cgr.mm"
include "nvgrp.mm"
include "bafval.mm"
include "eqid.mm"
include "grpolid.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem nv0lid
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let cZ: class Z
  assume nv0id.1: |- X = ( BaseSet ` U )
  assume nv0id.2: |- G = ( +v ` U )
  assume nv0id.6: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z G A ) = A )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cZ
    cA
    cG
    co
    #
    cG
    cgi
    cfv
    #
    cA
    cG
    co
    #
    cA
    @0
    @2
    @4
    wceq
    @1
    @0
    cZ
    @3
    cA
    cG
    cU
    cG
    cnv
    cZ
    nv0id.2
    nv0id.6
    0vfval
    oveq1d
    adantr
    @0
    cG
    cgr
    wcel
    @1
    @4
    cA
    wceq
    cU
    cG
    nv0id.2
    nvgrp
    cA
    @3
    cG
    cX
    cU
    cG
    cX
    nv0id.1
    nv0id.2
    bafval
    @3
    eqid
    grpolid
    sylan
    eqtrd
end
