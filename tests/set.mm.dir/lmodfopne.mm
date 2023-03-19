include "clmod.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "lmodfopnelem2.mm"
include "c0g.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "simpl.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "adantr.mm"
include "plusfval.mm"
include "eqcomd.mm"
include "syl2anr.mm"
include "oveq.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grprid.mm"
include "syl2an.mm"
include "cvsca.mm"
include "lmod0cl.mm"
include "jca.mm"
include "scafval.mm"
include "syl.mm"
include "ancli.mm"
include "lmodvs0.mm"
include "simpr.mm"
include "lmod1cl.mm"
include "lmodvs1.mm"
include "ad2ant2rl.mm"
include "adantl.mm"
include "3eqtr2d.mm"
include "wb.mm"
include "grplcan.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "3eqtrd.mm"
include "3eqtr3rd.mm"
include "mpdan.mm"
include "ex.mm"
include "necon3d.mm"
include "imp.mm"

theorem lmodfopne
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lmodfopne.t: |- .x. = ( .sf ` W )
  assume lmodfopne.a: |- .+ = ( +f ` W )
  assume lmodfopne.v: |- V = ( Base ` W )
  assume lmodfopne.s: |- S = ( Scalar ` W )
  assume lmodfopne.k: |- K = ( Base ` S )
  assume lmodfopne.0: |- .0. = ( 0g ` S )
  assume lmodfopne.1: |- .1. = ( 1r ` S )


  assert |- ( ( W e. LMod /\ .1. =/= .0. ) -> .+ =/= .x. )

  proof
    cW
    clmod
    wcel
    #
    c.1
    c.0
    wne
    c.pl
    c.x
    wne
    @0
    c.pl
    c.x
    c.1
    c.0
    @0
    c.pl
    c.x
    wceq
    #
    c.1
    c.0
    wceq
    #
    @0
    @1
    wa
    #
    c.0
    cV
    wcel
    #
    c.1
    cV
    wcel
    #
    wa
    #
    @2
    c.pl
    cS
    c.x
    c.1
    cK
    cV
    cW
    c.0
    lmodfopne.t
    lmodfopne.a
    lmodfopne.v
    lmodfopne.s
    lmodfopne.k
    lmodfopne.0
    lmodfopne.1
    lmodfopnelem2
    @3
    @6
    wa
    #
    c.0
    cW
    c0g
    cfv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    c.0
    @8
    c.x
    co
    #
    c.0
    c.1
    @7
    @10
    c.0
    @8
    c.pl
    co
    #
    @11
    @6
    @4
    @8
    cV
    wcel
    #
    @10
    @12
    wceq
    @3
    @4
    @5
    simpl
    #
    @0
    @13
    @1
    cV
    cW
    @8
    lmodfopne.v
    @8
    eqid
    #
    lmod0vcl
    #
    adantr
    #
    @4
    @13
    wa
    @12
    @10
    cV
    @9
    c.pl
    cW
    c.0
    @8
    lmodfopne.v
    @9
    eqid
    #
    lmodfopne.a
    plusfval
    eqcomd
    syl2anr
    @1
    @12
    @11
    wceq
    @0
    @6
    c.0
    @8
    c.pl
    c.x
    oveq
    ad2antlr
    eqtrd
    @3
    cW
    cgrp
    wcel
    #
    @4
    @10
    c.0
    wceq
    @6
    @0
    @19
    @1
    cW
    lmodgrp
    adantr
    #
    @14
    cV
    @9
    cW
    c.0
    @8
    lmodfopne.v
    @18
    @15
    grprid
    syl2an
    @7
    @11
    c.0
    @8
    cW
    cvsca
    cfv
    #
    co
    #
    @8
    c.1
    @7
    c.0
    cK
    wcel
    #
    @13
    wa
    #
    @11
    @22
    wceq
    @3
    @24
    @6
    @0
    @24
    @1
    @0
    @23
    @13
    cS
    cK
    cW
    c.0
    lmodfopne.s
    lmodfopne.k
    lmodfopne.0
    lmod0cl
    #
    @16
    jca
    adantr
    adantr
    cV
    c.x
    @21
    cS
    cK
    cW
    c.0
    @8
    lmodfopne.v
    lmodfopne.s
    lmodfopne.k
    lmodfopne.t
    @21
    eqid
    #
    scafval
    syl
    @7
    @0
    @23
    wa
    #
    @22
    @8
    wceq
    @3
    @27
    @6
    @0
    @27
    @1
    @0
    @23
    @25
    ancli
    adantr
    adantr
    @21
    cS
    cK
    cW
    c.0
    @8
    lmodfopne.s
    @26
    lmodfopne.k
    @15
    lmodvs0
    syl
    @7
    c.1
    @8
    @9
    co
    #
    c.1
    c.1
    @9
    co
    #
    wceq
    #
    @8
    c.1
    wceq
    #
    @7
    @28
    c.1
    c.1
    c.1
    c.x
    co
    #
    @29
    @3
    @19
    @5
    @28
    c.1
    wceq
    @6
    @20
    @4
    @5
    simpr
    #
    cV
    @9
    cW
    c.1
    @8
    lmodfopne.v
    @18
    @15
    grprid
    syl2an
    @7
    @32
    c.1
    c.1
    @21
    co
    #
    c.1
    @3
    c.1
    cK
    wcel
    #
    @5
    @32
    @34
    wceq
    @6
    @0
    @35
    @1
    c.1
    cS
    cK
    cW
    lmodfopne.s
    lmodfopne.k
    lmodfopne.1
    lmod1cl
    adantr
    @33
    cV
    c.x
    @21
    cS
    cK
    cW
    c.1
    c.1
    lmodfopne.v
    lmodfopne.s
    lmodfopne.k
    lmodfopne.t
    @26
    scafval
    syl2an
    @0
    @5
    @34
    c.1
    wceq
    @1
    @4
    @21
    c.1
    cS
    cV
    cW
    c.1
    lmodfopne.v
    lmodfopne.s
    @26
    lmodfopne.1
    lmodvs1
    ad2ant2rl
    eqtrd
    @7
    @32
    c.1
    c.1
    c.pl
    co
    #
    @29
    @1
    @32
    @36
    wceq
    @0
    @6
    @1
    @36
    @32
    c.1
    c.1
    c.pl
    c.x
    oveq
    eqcomd
    ad2antlr
    @7
    @5
    @5
    wa
    #
    @36
    @29
    wceq
    @6
    @37
    @3
    @6
    @5
    @5
    @33
    @33
    jca
    adantl
    cV
    @9
    c.pl
    cW
    c.1
    c.1
    lmodfopne.v
    @18
    lmodfopne.a
    plusfval
    syl
    eqtrd
    3eqtr2d
    @7
    @19
    @13
    @5
    @5
    @30
    @31
    wb
    @3
    @19
    @6
    @20
    adantr
    @3
    @13
    @6
    @17
    adantr
    @6
    @5
    @3
    @33
    adantl
    #
    @38
    cV
    @9
    cW
    @8
    c.1
    c.1
    lmodfopne.v
    @18
    grplcan
    syl13anc
    mpbid
    3eqtrd
    3eqtr3rd
    mpdan
    ex
    necon3d
    imp
end
