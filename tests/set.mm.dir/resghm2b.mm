include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "cgrp.mm"
include "cghm.mm"
include "co.mm"
include "wi.mm"
include "ghmgrp1.mm"
include "a1i.mm"
include "wb.mm"
include "cmhm.mm"
include "csubmnd.mm"
include "subgsubm.mm"
include "resmhm2b.mm"
include "sylan.mm"
include "adantl.mm"
include "wceq.mm"
include "subgrcl.mm"
include "adantr.mm"
include "ghmmhmb.mm"
include "sylan2.mm"
include "eleq2d.mm"
include "subggrp.mm"
include "3bitr4d.mm"
include "expcom.mm"
include "pm5.21ndd.mm"

theorem resghm2b
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  assume resghm2.u: |- U = ( T |`s X )


  assert |- ( ( X e. ( SubGrp ` T ) /\ ran F C_ X ) -> ( F e. ( S GrpHom T ) <-> F e. ( S GrpHom U ) ) )

  proof
    cX
    cT
    csubg
    cfv
    wcel
    #
    cF
    crn
    cX
    wss
    #
    wa
    #
    cS
    cgrp
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    #
    cF
    cS
    cU
    cghm
    co
    #
    wcel
    #
    @5
    @3
    wi
    @2
    cS
    cT
    cF
    ghmgrp1
    a1i
    @7
    @3
    wi
    @2
    cS
    cU
    cF
    ghmgrp1
    a1i
    @3
    @2
    @5
    @7
    wb
    @3
    @2
    wa
    #
    cF
    cS
    cT
    cmhm
    co
    #
    wcel
    #
    cF
    cS
    cU
    cmhm
    co
    #
    wcel
    #
    @5
    @7
    @2
    @10
    @12
    wb
    #
    @3
    @0
    cX
    cT
    csubmnd
    cfv
    wcel
    @1
    @13
    cX
    cT
    subgsubm
    cS
    cT
    cU
    cF
    cX
    resghm2.u
    resmhm2b
    sylan
    adantl
    @8
    @4
    @9
    cF
    @2
    @3
    cT
    cgrp
    wcel
    #
    @4
    @9
    wceq
    @0
    @14
    @1
    cX
    cT
    subgrcl
    adantr
    cS
    cT
    ghmmhmb
    sylan2
    eleq2d
    @8
    @6
    @11
    cF
    @2
    @3
    cU
    cgrp
    wcel
    #
    @6
    @11
    wceq
    @0
    @15
    @1
    cX
    cT
    cU
    resghm2.u
    subggrp
    adantr
    cS
    cU
    ghmmhmb
    sylan2
    eleq2d
    3bitr4d
    expcom
    pm5.21ndd
end
