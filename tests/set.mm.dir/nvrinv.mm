include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cgn.mm"
include "cfv.mm"
include "co.mm"
include "cgi.mm"
include "c1.mm"
include "cneg.mm"
include "cgr.mm"
include "wceq.mm"
include "nvgrp.mm"
include "bafval.mm"
include "eqid.mm"
include "grporinv.mm"
include "sylan.mm"
include "nvinv.mm"
include "oveq2d.mm"
include "0vfval.mm"
include "adantr.mm"
include "3eqtr4d.mm"

theorem nvrinv
  let cA: class A
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let cZ: class Z
  assume nvrinv.1: |- X = ( BaseSet ` U )
  assume nvrinv.2: |- G = ( +v ` U )
  assume nvrinv.4: |- S = ( .sOLD ` U )
  assume nvrinv.6: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G ( -u 1 S A ) ) = Z )

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
    #
    cA
    cA
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cG
    cgi
    cfv
    #
    cA
    c1
    cneg
    cA
    cS
    co
    #
    cG
    co
    cZ
    @0
    cG
    cgr
    wcel
    @1
    @5
    @6
    wceq
    cU
    cG
    nvrinv.2
    nvgrp
    cA
    @6
    cG
    @3
    cX
    cU
    cG
    cX
    nvrinv.1
    nvrinv.2
    bafval
    @6
    eqid
    @3
    eqid
    #
    grporinv
    sylan
    @2
    @7
    @4
    cA
    cG
    cA
    cS
    cU
    cG
    @3
    cX
    nvrinv.1
    nvrinv.2
    nvrinv.4
    @8
    nvinv
    oveq2d
    @0
    cZ
    @6
    wceq
    @1
    cU
    cG
    cnv
    cZ
    nvrinv.2
    nvrinv.6
    0vfval
    adantr
    3eqtr4d
end
