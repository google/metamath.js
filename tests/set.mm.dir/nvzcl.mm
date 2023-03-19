include "cnv.mm"
include "wcel.mm"
include "cpv.mm"
include "cfv.mm"
include "cgi.mm"
include "eqid.mm"
include "0vfval.mm"
include "cgr.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grpoidcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem nvzcl
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume nvzcl.1: |- X = ( BaseSet ` U )
  assume nvzcl.6: |- Z = ( 0vec ` U )


  assert |- ( U e. NrmCVec -> Z e. X )

  proof
    cU
    cnv
    wcel
    #
    cZ
    cU
    cpv
    cfv
    #
    cgi
    cfv
    #
    cX
    cU
    @1
    cnv
    cZ
    @1
    eqid
    #
    nvzcl.6
    0vfval
    @0
    @1
    cgr
    wcel
    @2
    cX
    wcel
    cU
    @1
    @3
    nvgrp
    @2
    @1
    cX
    cU
    @1
    cX
    nvzcl.1
    @3
    bafval
    @2
    eqid
    grpoidcl
    syl
    eqeltrd
end
