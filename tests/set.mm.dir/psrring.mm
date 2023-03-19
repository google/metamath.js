include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "eqidd.mm"
include "crg.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "psrgrp.mm"
include "w3a.mm"
include "eqid.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "psrmulcl.mm"
include "wa.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "psrass1.mm"
include "psrdi.mm"
include "psrdir.mm"
include "psr1cl.mm"
include "simpr.mm"
include "psrlidm.mm"
include "psrridm.mm"
include "isringd.mm"

theorem psrring
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  let c.pl: class .+
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cK: class K
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cX: class X
  let c.x: class .x.
  let cZ: class Z
  let c.1: class .1.
  let c.xp: class .X.
  let cY: class Y
  assume psrring.s: |- S = ( I mPwSer R )
  assume psrring.i: |- ( ph -> I e. V )
  assume psrring.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> S e. Ring )

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
    cS
    cmulr
    cfv
    #
    vr
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    vr
    cv
    cI
    cc0
    csn
    cxp
    wceq
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    cmpt
    #
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    wph
    @2
    eqidd
    wph
    cR
    cS
    cI
    cV
    psrring.s
    psrring.i
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    psrring.r
    cR
    ringgrp
    syl
    psrgrp
    wph
    vx
    cv
    #
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
    cR
    cS
    @2
    cI
    @8
    @10
    psrring.s
    @0
    eqid
    #
    @2
    eqid
    #
    wph
    @9
    @7
    @11
    psrring.r
    3ad2ant1
    wph
    @9
    @11
    simp2
    wph
    @9
    @11
    simp3
    psrmulcl
    wph
    @9
    @11
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
    @0
    @3
    cR
    cS
    @2
    vf
    cI
    cV
    @8
    @10
    @14
    psrring.s
    wph
    cI
    cV
    wcel
    #
    @16
    psrring.i
    adantr
    #
    wph
    @7
    @16
    psrring.r
    adantr
    #
    @3
    eqid
    #
    @13
    @12
    wph
    @9
    @11
    @15
    simpr1
    #
    wph
    @9
    @11
    @15
    simpr2
    #
    wph
    @9
    @11
    @15
    simpr3
    #
    psrass1
    @17
    @0
    @3
    @1
    cR
    cS
    @2
    vf
    cI
    cV
    @8
    @10
    @14
    psrring.s
    @19
    @20
    @21
    @13
    @12
    @22
    @23
    @24
    @1
    eqid
    #
    psrdi
    @17
    @0
    @3
    @1
    cR
    cS
    @2
    vf
    cI
    cV
    @8
    @10
    @14
    psrring.s
    @19
    @20
    @21
    @13
    @12
    @22
    @23
    @24
    @25
    psrdir
    wph
    vr
    @0
    @3
    cR
    cS
    @6
    @4
    vf
    cI
    cV
    @5
    psrring.s
    psrring.i
    psrring.r
    @21
    @5
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    @12
    psr1cl
    wph
    @9
    wa
    #
    vr
    @0
    @3
    cR
    cS
    @2
    @6
    @4
    vf
    cI
    cV
    @8
    @5
    psrring.s
    wph
    @18
    @9
    psrring.i
    adantr
    #
    wph
    @7
    @9
    psrring.r
    adantr
    #
    @21
    @26
    @27
    @28
    @12
    @13
    wph
    @9
    simpr
    #
    psrlidm
    @29
    vr
    @0
    @3
    cR
    cS
    @2
    @6
    @4
    vf
    cI
    cV
    @8
    @5
    psrring.s
    @30
    @31
    @21
    @26
    @27
    @28
    @12
    @13
    @32
    psrridm
    isringd
end
