include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cmhm.mm"
include "csubmnd.mm"
include "ghmmhm.mm"
include "subgsubm.mm"
include "resmhm2.mm"
include "syl2an.mm"
include "cgrp.mm"
include "wceq.mm"
include "ghmgrp1.mm"
include "subgrcl.mm"
include "ghmmhmb.mm"
include "eleqtrrd.mm"

theorem resghm2
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  assume resghm2.u: |- U = ( T |`s X )


  assert |- ( ( F e. ( S GrpHom U ) /\ X e. ( SubGrp ` T ) ) -> F e. ( S GrpHom T ) )

  proof
    cF
    cS
    cU
    cghm
    co
    wcel
    #
    cX
    cT
    csubg
    cfv
    wcel
    #
    wa
    cF
    cS
    cT
    cmhm
    co
    #
    cS
    cT
    cghm
    co
    #
    @0
    cF
    cS
    cU
    cmhm
    co
    wcel
    cX
    cT
    csubmnd
    cfv
    wcel
    cF
    @2
    wcel
    @1
    cS
    cU
    cF
    ghmmhm
    cX
    cT
    subgsubm
    cS
    cT
    cU
    cF
    cX
    resghm2.u
    resmhm2
    syl2an
    @0
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    @3
    @2
    wceq
    @1
    cS
    cU
    cF
    ghmgrp1
    cX
    cT
    subgrcl
    cS
    cT
    ghmmhmb
    syl2an
    eleqtrrd
end
