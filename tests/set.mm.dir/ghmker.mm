include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cnsg.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "cgrp.mm"
include "ghmgrp2.mm"
include "0nsg.mm"
include "syl.mm"
include "ghmnsgpreima.mm"
include "mpdan.mm"

theorem ghmker
  let cS: class S
  let cT: class T
  let cF: class F
  let c.0: class .0.
  assume ghmker.1: |- .0. = ( 0g ` T )


  assert |- ( F e. ( S GrpHom T ) -> ( `' F " { .0. } ) e. ( NrmSGrp ` S ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    c.0
    csn
    #
    cT
    cnsg
    cfv
    wcel
    #
    cF
    ccnv
    @1
    cima
    cS
    cnsg
    cfv
    wcel
    @0
    cT
    cgrp
    wcel
    @2
    cS
    cT
    cF
    ghmgrp2
    cT
    c.0
    ghmker.1
    0nsg
    syl
    cS
    cT
    cF
    @1
    ghmnsgpreima
    mpdan
end
