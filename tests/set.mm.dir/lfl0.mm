include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "cplusg.mm"
include "cur.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "lmod1cl.mm"
include "adantr.mm"
include "lmod0vcl.mm"
include "lfli.mm"
include "syl113anc.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmod0vrid.mm"
include "syldan.mm"
include "lmodvs1.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "crg.mm"
include "lmodring.mm"
include "lflcl.mm"
include "mpd3an3.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "grpsubid.mm"
include "grppncan.mm"
include "3eqtr3rd.mm"

theorem lfl0
  let cD: class D
  let cF: class F
  let cG: class G
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  assume lfl0.d: |- D = ( Scalar ` W )
  assume lfl0.o: |- .0. = ( 0g ` D )
  assume lfl0.z: |- Z = ( 0g ` W )
  assume lfl0.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. LMod /\ G e. F ) -> ( G ` Z ) = .0. )

  proof
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    wa
    #
    cZ
    cG
    cfv
    #
    @3
    cD
    csg
    cfv
    #
    co
    #
    @3
    @3
    cD
    cplusg
    cfv
    #
    co
    #
    @3
    @4
    co
    #
    c.0
    @3
    @2
    @3
    @7
    @3
    @4
    @2
    cD
    cur
    cfv
    #
    cZ
    cW
    cvsca
    cfv
    #
    co
    #
    cZ
    cW
    cplusg
    cfv
    #
    co
    #
    cG
    cfv
    #
    @9
    @3
    cD
    cmulr
    cfv
    #
    co
    #
    @3
    @6
    co
    #
    @3
    @7
    @2
    @0
    @1
    @9
    cD
    cbs
    cfv
    #
    wcel
    #
    cZ
    cW
    cbs
    cfv
    #
    wcel
    #
    @21
    @14
    @17
    wceq
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    @0
    @19
    @1
    @9
    cD
    @18
    cW
    lfl0.d
    @18
    eqid
    #
    @9
    eqid
    #
    lmod1cl
    adantr
    #
    @0
    @21
    @1
    @20
    cW
    cZ
    @20
    eqid
    #
    lfl0.z
    lmod0vcl
    adantr
    #
    @27
    cD
    @12
    @6
    @9
    @10
    @15
    cF
    cG
    @18
    @20
    cW
    cZ
    cZ
    clmod
    @26
    @12
    eqid
    #
    lfl0.d
    @10
    eqid
    #
    @23
    @6
    eqid
    #
    @15
    eqid
    #
    lfl0.f
    lfli
    syl113anc
    @2
    @13
    cZ
    cG
    @2
    @13
    @11
    cZ
    @0
    @1
    @11
    @20
    wcel
    #
    @13
    @11
    wceq
    @2
    @0
    @19
    @21
    @32
    @22
    @25
    @27
    @9
    @10
    cD
    @18
    @20
    cW
    cZ
    @26
    lfl0.d
    @29
    @23
    lmodvscl
    syl3anc
    @12
    @20
    cW
    @11
    cZ
    @26
    @28
    lfl0.z
    lmod0vrid
    syldan
    @0
    @1
    @21
    @11
    cZ
    wceq
    @27
    @10
    @9
    cD
    @20
    cW
    cZ
    @26
    lfl0.d
    @29
    @24
    lmodvs1
    syldan
    eqtrd
    fveq2d
    @2
    @16
    @3
    @3
    @6
    @2
    cD
    crg
    wcel
    #
    @3
    @18
    wcel
    #
    @16
    @3
    wceq
    @0
    @33
    @1
    cD
    cW
    lfl0.d
    lmodring
    adantr
    #
    @0
    @1
    @21
    @34
    @27
    cD
    cF
    cG
    @18
    @20
    cW
    cZ
    clmod
    lfl0.d
    @23
    @26
    lfl0.f
    lflcl
    mpd3an3
    #
    @18
    cD
    @15
    @9
    @3
    @23
    @31
    @24
    ringlidm
    syl2anc
    oveq1d
    3eqtr3d
    oveq1d
    @2
    cD
    cgrp
    wcel
    #
    @34
    @5
    c.0
    wceq
    @2
    @33
    @37
    @35
    cD
    ringgrp
    syl
    #
    @36
    @18
    cD
    @4
    @3
    c.0
    @23
    lfl0.o
    @4
    eqid
    #
    grpsubid
    syl2anc
    @2
    @37
    @34
    @34
    @8
    @3
    wceq
    @38
    @36
    @36
    @18
    @6
    cD
    @4
    @3
    @3
    @23
    @30
    @39
    grppncan
    syl3anc
    3eqtr3rd
end
