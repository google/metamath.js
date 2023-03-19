include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgm.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "csgrp.mm"
include "lidlmmgm.mm"
include "w3a.mm"
include "cmnd.mm"
include "eqid.mm"
include "ringmgp.mm"
include "ad2antrr.mm"
include "wi.mm"
include "lidlssbas.mm"
include "sseld.mm"
include "3anim123d.mm"
include "adantl.mm"
include "imp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndass.mm"
include "syl2anc.mm"
include "ralrimivvva.mm"
include "wb.mm"
include "ressmulr.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "mpbird.mm"
include "issgrp.mm"
include "sylanbrc.mm"

theorem lidlmsgrp
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )


  assert |- ( ( R e. Ring /\ U e. L ) -> ( mulGrp ` I ) e. SGrp )

  proof
    cR
    crg
    wcel
    #
    cU
    cL
    wcel
    #
    wa
    #
    cI
    cmgp
    cfv
    #
    cmgm
    wcel
    va
    cv
    #
    vb
    cv
    #
    cI
    cmulr
    cfv
    #
    co
    #
    vc
    cv
    #
    @6
    co
    #
    @4
    @5
    @8
    @6
    co
    #
    @6
    co
    #
    wceq
    #
    vc
    cI
    cbs
    cfv
    #
    wral
    #
    vb
    @13
    wral
    va
    @13
    wral
    #
    @3
    csgrp
    wcel
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlmmgm
    @2
    @15
    @4
    @5
    cR
    cmulr
    cfv
    #
    co
    #
    @8
    @16
    co
    #
    @4
    @5
    @8
    @16
    co
    #
    @16
    co
    #
    wceq
    #
    vc
    @13
    wral
    #
    vb
    @13
    wral
    va
    @13
    wral
    @2
    @21
    va
    vb
    vc
    @13
    @13
    @13
    @2
    @4
    @13
    wcel
    #
    @5
    @13
    wcel
    #
    @8
    @13
    wcel
    #
    w3a
    #
    wa
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @4
    cR
    cbs
    cfv
    #
    wcel
    #
    @5
    @29
    wcel
    #
    @8
    @29
    wcel
    #
    w3a
    #
    @21
    @0
    @28
    @1
    @26
    cR
    @27
    @27
    eqid
    #
    ringmgp
    ad2antrr
    @2
    @26
    @33
    @1
    @26
    @33
    wi
    @0
    @1
    @23
    @30
    @24
    @31
    @25
    @32
    @1
    @13
    @29
    @4
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlssbas
    #
    sseld
    @1
    @13
    @29
    @5
    @35
    sseld
    @1
    @13
    @29
    @8
    @35
    sseld
    3anim123d
    adantl
    imp
    @29
    @16
    @27
    @4
    @5
    @8
    @29
    cR
    @27
    @34
    @29
    eqid
    mgpbas
    cR
    @16
    @27
    @34
    @16
    eqid
    #
    mgpplusg
    mndass
    syl2anc
    ralrimivvva
    @2
    @14
    @22
    va
    vb
    @13
    @13
    @2
    @12
    @21
    vc
    @13
    @1
    @12
    @21
    wb
    @0
    @1
    @9
    @18
    @11
    @20
    @1
    @7
    @17
    @8
    @8
    @6
    @16
    @1
    @16
    @6
    cU
    cR
    cI
    @16
    cL
    lidlabl.i
    @36
    ressmulr
    eqcomd
    #
    @1
    @6
    @16
    @4
    @5
    @37
    oveqd
    @1
    @8
    eqidd
    oveq123d
    @1
    @4
    @4
    @10
    @19
    @6
    @16
    @37
    @1
    @4
    eqidd
    @1
    @6
    @16
    @5
    @8
    @37
    oveqd
    oveq123d
    eqeq12d
    adantl
    ralbidv
    2ralbidv
    mpbird
    va
    vb
    vc
    @13
    @3
    @6
    @13
    cI
    @3
    @3
    eqid
    #
    @13
    eqid
    mgpbas
    cI
    @6
    @3
    @38
    @6
    eqid
    mgpplusg
    issgrp
    sylanbrc
end
