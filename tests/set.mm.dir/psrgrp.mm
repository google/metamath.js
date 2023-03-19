include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cminusg.mm"
include "cv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "eqidd.mm"
include "w3a.mm"
include "eqid.mm"
include "cgrp.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "psraddcl.mm"
include "wa.mm"
include "cof.mm"
include "cvv.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "simpr1.mm"
include "psrelbas.mm"
include "simpr2.mm"
include "simpr3.mm"
include "wceq.mm"
include "adantr.mm"
include "grpass.mm"
include "sylan.mm"
include "caofass.mm"
include "psradd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "3adant3r3.mm"
include "psr0cl.mm"
include "simpr.mm"
include "psr0lid.mm"
include "psrnegcl.mm"
include "psrlinv.mm"
include "isgrpd.mm"

theorem psrgrp
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let vf: setvar f
  let cN: class N
  let cX: class X
  assume psrgrp.s: |- S = ( I mPwSer R )
  assume psrgrp.i: |- ( ph -> I e. V )
  assume psrgrp.r: |- ( ph -> R e. Grp )


  assert |- ( ph -> S e. Grp )

  proof
    wph
    vx
    vy
    vz
    cS
    cbs
    cfv
    #
    cS
    cplusg
    cfv
    #
    cS
    cR
    cminusg
    cfv
    #
    vx
    cv
    #
    ccom
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vf
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cR
    c0g
    cfv
    #
    csn
    cxp
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    wph
    @3
    @0
    wcel
    #
    vy
    cv
    #
    @0
    wcel
    #
    w3a
    @0
    @1
    cR
    cS
    cI
    @3
    @9
    psrgrp.s
    @0
    eqid
    #
    @1
    eqid
    #
    wph
    @8
    cR
    cgrp
    wcel
    #
    @10
    psrgrp.r
    3ad2ant1
    wph
    @8
    @10
    simp2
    wph
    @8
    @10
    simp3
    psraddcl
    #
    wph
    @8
    @10
    vz
    cv
    #
    @0
    wcel
    #
    w3a
    #
    wa
    #
    @3
    @9
    @1
    co
    #
    @15
    cR
    cplusg
    cfv
    #
    cof
    #
    co
    #
    @3
    @9
    @15
    @1
    co
    #
    @21
    co
    #
    @19
    @15
    @1
    co
    @3
    @23
    @1
    co
    @18
    @3
    @9
    @21
    co
    #
    @15
    @21
    co
    @3
    @9
    @15
    @21
    co
    #
    @21
    co
    @22
    @24
    @18
    vr
    vs
    vt
    @6
    @20
    @20
    cR
    cbs
    cfv
    #
    @20
    @3
    @9
    @15
    @20
    cvv
    @6
    cvv
    wcel
    @18
    @4
    vf
    @5
    cn0
    cI
    cmap
    ovex
    rabex
    a1i
    @18
    @0
    @6
    cR
    cS
    vf
    cI
    @27
    @3
    psrgrp.s
    @27
    eqid
    #
    @6
    eqid
    #
    @11
    wph
    @8
    @10
    @16
    simpr1
    #
    psrelbas
    @18
    @0
    @6
    cR
    cS
    vf
    cI
    @27
    @9
    psrgrp.s
    @28
    @29
    @11
    wph
    @8
    @10
    @16
    simpr2
    #
    psrelbas
    @18
    @0
    @6
    cR
    cS
    vf
    cI
    @27
    @15
    psrgrp.s
    @28
    @29
    @11
    wph
    @8
    @10
    @16
    simpr3
    #
    psrelbas
    @18
    @13
    vr
    cv
    #
    @27
    wcel
    vs
    cv
    #
    @27
    wcel
    vt
    cv
    #
    @27
    wcel
    w3a
    @33
    @34
    @20
    co
    @35
    @20
    co
    @33
    @34
    @35
    @20
    co
    @20
    co
    wceq
    wph
    @13
    @17
    psrgrp.r
    adantr
    #
    @27
    @20
    cR
    @33
    @34
    @35
    @28
    @20
    eqid
    #
    grpass
    sylan
    caofass
    @18
    @19
    @25
    @15
    @21
    @18
    @0
    @20
    @1
    cR
    cS
    cI
    @3
    @9
    psrgrp.s
    @11
    @37
    @12
    @30
    @31
    psradd
    oveq1d
    @18
    @23
    @26
    @3
    @21
    @18
    @0
    @20
    @1
    cR
    cS
    cI
    @9
    @15
    psrgrp.s
    @11
    @37
    @12
    @31
    @32
    psradd
    oveq2d
    3eqtr4d
    @18
    @0
    @20
    @1
    cR
    cS
    cI
    @19
    @15
    psrgrp.s
    @11
    @37
    @12
    wph
    @8
    @10
    @19
    @0
    wcel
    @16
    @14
    3adant3r3
    @32
    psradd
    @18
    @0
    @20
    @1
    cR
    cS
    cI
    @3
    @23
    psrgrp.s
    @11
    @37
    @12
    @30
    @18
    @0
    @1
    cR
    cS
    cI
    @9
    @15
    psrgrp.s
    @11
    @12
    @36
    @31
    @32
    psraddcl
    psradd
    3eqtr4d
    wph
    @0
    @6
    cR
    cS
    vf
    cI
    cV
    @7
    psrgrp.s
    psrgrp.i
    psrgrp.r
    @29
    @7
    eqid
    #
    @11
    psr0cl
    wph
    @8
    wa
    #
    @0
    @6
    @1
    cR
    cS
    vf
    cI
    cV
    @3
    @7
    psrgrp.s
    wph
    cI
    cV
    wcel
    @8
    psrgrp.i
    adantr
    #
    wph
    @13
    @8
    psrgrp.r
    adantr
    #
    @29
    @38
    @11
    @12
    wph
    @8
    simpr
    #
    psr0lid
    @39
    @0
    @6
    cR
    cS
    vf
    cI
    @2
    cV
    @3
    psrgrp.s
    @40
    @41
    @29
    @2
    eqid
    #
    @11
    @42
    psrnegcl
    @39
    @0
    @6
    @1
    cR
    cS
    vf
    cI
    @2
    cV
    @3
    @7
    psrgrp.s
    @40
    @41
    @29
    @43
    @11
    @42
    @38
    @12
    psrlinv
    isgrpd
end
