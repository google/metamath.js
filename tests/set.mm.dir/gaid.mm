include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "c2nd.mm"
include "cres.mm"
include "wf.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "cga.mm"
include "elex.mm"
include "anim2i.mm"
include "eqid.mm"
include "grpidcl.mm"
include "adantr.mm"
include "ovres.mm"
include "cop.mm"
include "df-ov.mm"
include "fvex.mm"
include "vex.mm"
include "op2nd.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "sylan.mm"
include "simprl.mm"
include "simplr.mm"
include "syl2anc.mm"
include "simprr.mm"
include "oveq2d.mm"
include "simpll.mm"
include "grpcl.mm"
include "3expb.mm"
include "ovex.mm"
include "3eqtr4rd.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ralrimiva.mm"
include "f2ndres.mm"
include "jctil.mm"
include "isga.mm"
include "sylanbrc.mm"

theorem gaid
  let cS: class S
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gaid.1: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ S e. V ) -> ( 2nd |` ( X X. S ) ) e. ( G GrpAct S ) )

  proof
    cG
    cgrp
    wcel
    #
    cS
    cV
    wcel
    #
    wa
    #
    @0
    cS
    cvv
    wcel
    #
    wa
    cX
    cS
    cxp
    #
    cS
    c2nd
    @4
    cres
    #
    wf
    #
    cG
    c0g
    cfv
    #
    vx
    cv
    #
    @5
    co
    #
    @8
    wceq
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @8
    @5
    co
    #
    @11
    @12
    @8
    @5
    co
    #
    @5
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    wa
    #
    vx
    cS
    wral
    #
    wa
    @5
    cG
    cS
    cga
    co
    wcel
    @1
    @3
    @0
    cS
    cV
    elex
    anim2i
    @2
    @21
    @6
    @2
    @20
    vx
    cS
    @2
    @8
    cS
    wcel
    #
    wa
    #
    @10
    @19
    @2
    @7
    cX
    wcel
    #
    @22
    @10
    @0
    @24
    @1
    cX
    cG
    @7
    gaid.1
    @7
    eqid
    #
    grpidcl
    adantr
    @24
    @22
    wa
    @9
    @7
    @8
    c2nd
    co
    #
    @8
    @7
    @8
    cX
    cS
    c2nd
    ovres
    @26
    @7
    @8
    cop
    c2nd
    cfv
    @8
    @7
    @8
    c2nd
    df-ov
    @7
    @8
    cG
    c0g
    fvex
    vx
    vex
    #
    op2nd
    eqtri
    syl6eq
    sylan
    @23
    @18
    vy
    vz
    cX
    cX
    @23
    @11
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    wa
    #
    wa
    #
    @11
    @8
    @5
    co
    #
    @8
    @17
    @15
    @31
    @28
    @22
    @32
    @8
    wceq
    @23
    @28
    @29
    simprl
    @2
    @22
    @30
    simplr
    #
    @28
    @22
    wa
    @32
    @11
    @8
    c2nd
    co
    #
    @8
    @11
    @8
    cX
    cS
    c2nd
    ovres
    @34
    @11
    @8
    cop
    c2nd
    cfv
    @8
    @11
    @8
    c2nd
    df-ov
    @11
    @8
    vy
    vex
    @27
    op2nd
    eqtri
    syl6eq
    syl2anc
    @31
    @16
    @8
    @11
    @5
    @31
    @29
    @22
    @16
    @8
    wceq
    @23
    @28
    @29
    simprr
    @33
    @29
    @22
    wa
    @16
    @12
    @8
    c2nd
    co
    #
    @8
    @12
    @8
    cX
    cS
    c2nd
    ovres
    @35
    @12
    @8
    cop
    c2nd
    cfv
    @8
    @12
    @8
    c2nd
    df-ov
    @12
    @8
    vz
    vex
    @27
    op2nd
    eqtri
    syl6eq
    syl2anc
    oveq2d
    @31
    @14
    cX
    wcel
    #
    @22
    @15
    @8
    wceq
    @23
    @0
    @30
    @36
    @0
    @1
    @22
    simpll
    @0
    @28
    @29
    @36
    cX
    @13
    cG
    @11
    @12
    gaid.1
    @13
    eqid
    #
    grpcl
    3expb
    sylan
    @33
    @36
    @22
    wa
    @15
    @14
    @8
    c2nd
    co
    #
    @8
    @14
    @8
    cX
    cS
    c2nd
    ovres
    @38
    @14
    @8
    cop
    c2nd
    cfv
    @8
    @14
    @8
    c2nd
    df-ov
    @14
    @8
    @11
    @12
    @13
    ovex
    @27
    op2nd
    eqtri
    syl6eq
    syl2anc
    3eqtr4rd
    ralrimivva
    jca
    ralrimiva
    cX
    cS
    f2ndres
    jctil
    vx
    vy
    vz
    @13
    @5
    cG
    cX
    cS
    @7
    gaid.1
    @37
    @25
    isga
    sylanbrc
end
