include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "eqid.mm"
include "lidlss.mm"
include "adantl.mm"
include "c0g.mm"
include "lidl0cl.mm"
include "ne0i.mm"
include "syl.mm"
include "lidlacl.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "lidlnegcl.mm"
include "3expa.mm"
include "jca.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "ringgrp.mm"
include "adantr.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem lidlsubg
  let cR: class R
  let cU: class U
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume lidlcl.u: |- U = ( LIdeal ` R )


  assert |- ( ( R e. Ring /\ I e. U ) -> I e. ( SubGrp ` R ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    #
    cI
    cR
    csubg
    cfv
    wcel
    #
    cI
    cR
    cbs
    cfv
    #
    wss
    #
    cI
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    cI
    wcel
    #
    vy
    cI
    wral
    #
    @7
    cR
    cminusg
    cfv
    #
    cfv
    cI
    wcel
    #
    wa
    #
    vx
    cI
    wral
    #
    @1
    @5
    @0
    @4
    cI
    cU
    cR
    @4
    eqid
    #
    lidlcl.u
    lidlss
    adantl
    @2
    cR
    c0g
    cfv
    #
    cI
    wcel
    @6
    cR
    cU
    cI
    @17
    lidlcl.u
    @17
    eqid
    lidl0cl
    cI
    @17
    ne0i
    syl
    @2
    @14
    vx
    cI
    @2
    @7
    cI
    wcel
    #
    wa
    #
    @11
    @13
    @19
    @10
    vy
    cI
    @2
    @18
    @8
    cI
    wcel
    @10
    @9
    cR
    cU
    cI
    @7
    @8
    lidlcl.u
    @9
    eqid
    #
    lidlacl
    anassrs
    ralrimiva
    @0
    @1
    @18
    @13
    cR
    cU
    cI
    @12
    @7
    lidlcl.u
    @12
    eqid
    #
    lidlnegcl
    3expa
    jca
    ralrimiva
    @2
    cR
    cgrp
    wcel
    #
    @3
    @5
    @6
    @15
    w3a
    wb
    @0
    @22
    @1
    cR
    ringgrp
    adantr
    vx
    vy
    @4
    @9
    cI
    cR
    @12
    @16
    @20
    @21
    issubg2
    syl
    mpbir3and
end
