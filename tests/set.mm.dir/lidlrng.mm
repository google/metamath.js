include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cabl.mm"
include "cmgp.mm"
include "cfv.mm"
include "csgrp.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "crng.mm"
include "lidlabl.mm"
include "lidlmsgrp.mm"
include "w3a.mm"
include "simpll.mm"
include "wi.mm"
include "lidlssbas.mm"
include "sseld.mm"
include "3anim123d.mm"
include "adantl.mm"
include "imp.mm"
include "eqid.mm"
include "ringdi.mm"
include "syl2anc.mm"
include "ringdir.mm"
include "jca.mm"
include "ralrimivvva.mm"
include "wb.mm"
include "ressmulr.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "mpbird.mm"
include "isrng.mm"
include "syl3anbrc.mm"

theorem lidlrng
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


  assert |- ( ( R e. Ring /\ U e. L ) -> I e. Rng )

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
    cabl
    wcel
    cI
    cmgp
    cfv
    #
    csgrp
    wcel
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cI
    cplusg
    cfv
    #
    co
    #
    cI
    cmulr
    cfv
    #
    co
    #
    @4
    @5
    @9
    co
    #
    @4
    @6
    @9
    co
    #
    @7
    co
    #
    wceq
    #
    @4
    @5
    @7
    co
    #
    @6
    @9
    co
    #
    @12
    @5
    @6
    @9
    co
    #
    @7
    co
    #
    wceq
    #
    wa
    #
    vc
    cI
    cbs
    cfv
    #
    wral
    #
    vb
    @21
    wral
    va
    @21
    wral
    #
    cI
    crng
    wcel
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlabl
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlmsgrp
    @2
    @23
    @4
    @5
    @6
    cR
    cplusg
    cfv
    #
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @4
    @5
    @26
    co
    #
    @4
    @6
    @26
    co
    #
    @24
    co
    #
    wceq
    #
    @4
    @5
    @24
    co
    #
    @6
    @26
    co
    #
    @29
    @5
    @6
    @26
    co
    #
    @24
    co
    #
    wceq
    #
    wa
    #
    vc
    @21
    wral
    #
    vb
    @21
    wral
    va
    @21
    wral
    @2
    @37
    va
    vb
    vc
    @21
    @21
    @21
    @2
    @4
    @21
    wcel
    #
    @5
    @21
    wcel
    #
    @6
    @21
    wcel
    #
    w3a
    #
    wa
    #
    @31
    @36
    @43
    @0
    @4
    cR
    cbs
    cfv
    #
    wcel
    #
    @5
    @44
    wcel
    #
    @6
    @44
    wcel
    #
    w3a
    #
    @31
    @0
    @1
    @42
    simpll
    #
    @2
    @42
    @48
    @1
    @42
    @48
    wi
    @0
    @1
    @39
    @45
    @40
    @46
    @41
    @47
    @1
    @21
    @44
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
    @21
    @44
    @5
    @50
    sseld
    @1
    @21
    @44
    @6
    @50
    sseld
    3anim123d
    adantl
    imp
    #
    @44
    @24
    cR
    @26
    @4
    @5
    @6
    @44
    eqid
    #
    @24
    eqid
    #
    @26
    eqid
    #
    ringdi
    syl2anc
    @43
    @0
    @48
    @36
    @49
    @51
    @44
    @24
    cR
    @26
    @4
    @5
    @6
    @52
    @53
    @54
    ringdir
    syl2anc
    jca
    ralrimivvva
    @2
    @22
    @38
    va
    vb
    @21
    @21
    @2
    @20
    @37
    vc
    @21
    @1
    @20
    @37
    wb
    @0
    @1
    @14
    @31
    @19
    @36
    @1
    @10
    @27
    @13
    @30
    @1
    @4
    @4
    @8
    @25
    @9
    @26
    @1
    @26
    @9
    cU
    cR
    cI
    @26
    cL
    lidlabl.i
    @54
    ressmulr
    eqcomd
    #
    @1
    @4
    eqidd
    @1
    @7
    @24
    @5
    @6
    @1
    @24
    @7
    cU
    @24
    cR
    cI
    cL
    lidlabl.i
    @53
    ressplusg
    eqcomd
    #
    oveqd
    oveq123d
    @1
    @11
    @28
    @12
    @29
    @7
    @24
    @56
    @1
    @9
    @26
    @4
    @5
    @55
    oveqd
    @1
    @9
    @26
    @4
    @6
    @55
    oveqd
    #
    oveq123d
    eqeq12d
    @1
    @16
    @33
    @18
    @35
    @1
    @15
    @32
    @6
    @6
    @9
    @26
    @55
    @1
    @7
    @24
    @4
    @5
    @56
    oveqd
    @1
    @6
    eqidd
    oveq123d
    @1
    @12
    @29
    @17
    @34
    @7
    @24
    @56
    @57
    @1
    @9
    @26
    @5
    @6
    @55
    oveqd
    oveq123d
    eqeq12d
    anbi12d
    adantl
    ralbidv
    2ralbidv
    mpbird
    va
    vb
    vc
    @21
    @7
    cI
    @9
    @3
    @21
    eqid
    @3
    eqid
    @7
    eqid
    @9
    eqid
    isrng
    syl3anbrc
end
