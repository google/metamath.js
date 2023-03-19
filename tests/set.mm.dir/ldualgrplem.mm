include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "cminusg.mm"
include "cmpt.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "cbs.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualvbase.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "wcel.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "ldualvaddcl.mm"
include "wa.mm"
include "co.mm"
include "cof.mm"
include "adantr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ldualvadd.mm"
include "oveq2d.mm"
include "simpr1.mm"
include "oveq1d.mm"
include "lfladdass.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"
include "lfl0f.mm"
include "syl.mm"
include "simpr.mm"
include "lfladd0l.mm"
include "eqtrd.mm"
include "lflnegcl.mm"
include "lflnegl.mm"
include "isgrpd.mm"

theorem ldualgrplem
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ldualgrp.d: |- D = ( LDual ` W )
  assume ldualgrp.w: |- ( ph -> W e. LMod )
  assume ldualgrp.v: |- V = ( Base ` W )
  assume ldualgrp.p: |- .+ = oF ( +g ` W )
  assume ldualgrp.f: |- F = ( LFnl ` W )
  assume ldualgrp.r: |- R = ( Scalar ` W )
  assume ldualgrp.k: |- K = ( Base ` R )
  assume ldualgrp.t: |- .X. = ( .r ` R )
  assume ldualgrp.o: |- O = ( oppR ` R )
  assume ldualgrp.s: |- .x. = ( .s ` D )


  assert |- ( ph -> D e. Grp )

  proof
    wph
    vx
    vy
    vz
    cF
    cD
    cplusg
    cfv
    #
    cD
    vz
    cV
    vz
    cv
    #
    vx
    cv
    #
    cfv
    cR
    cminusg
    cfv
    #
    cfv
    cmpt
    #
    cV
    cR
    c0g
    cfv
    #
    csn
    cxp
    #
    wph
    cD
    cbs
    cfv
    #
    cF
    wph
    cD
    cF
    @7
    cW
    clmod
    ldualgrp.f
    ldualgrp.d
    @7
    eqid
    ldualgrp.w
    ldualvbase
    eqcomd
    wph
    @0
    eqidd
    wph
    @2
    cF
    wcel
    #
    vy
    cv
    #
    cF
    wcel
    #
    w3a
    cD
    @0
    cF
    @2
    @9
    cW
    ldualgrp.f
    ldualgrp.d
    @0
    eqid
    #
    wph
    @8
    cW
    clmod
    wcel
    #
    @10
    ldualgrp.w
    3ad2ant1
    wph
    @8
    @10
    simp2
    wph
    @8
    @10
    simp3
    ldualvaddcl
    wph
    @8
    @10
    @1
    cF
    wcel
    #
    w3a
    #
    wa
    #
    @2
    @9
    @1
    @0
    co
    #
    cR
    cplusg
    cfv
    #
    cof
    #
    co
    @2
    @9
    @1
    @18
    co
    #
    @18
    co
    #
    @2
    @16
    @0
    co
    @2
    @9
    @0
    co
    #
    @1
    @0
    co
    #
    @15
    @16
    @19
    @2
    @18
    @15
    cD
    @17
    @0
    cR
    cF
    @9
    @1
    cW
    clmod
    ldualgrp.f
    ldualgrp.r
    @17
    eqid
    #
    ldualgrp.d
    @11
    wph
    @12
    @14
    ldualgrp.w
    adantr
    #
    wph
    @8
    @10
    @13
    simpr2
    #
    wph
    @8
    @10
    @13
    simpr3
    #
    ldualvadd
    oveq2d
    @15
    cD
    @17
    @0
    cR
    cF
    @2
    @16
    cW
    clmod
    ldualgrp.f
    ldualgrp.r
    @23
    ldualgrp.d
    @11
    @24
    wph
    @8
    @10
    @13
    simpr1
    #
    @15
    cD
    @0
    cF
    @9
    @1
    cW
    ldualgrp.f
    ldualgrp.d
    @11
    @24
    @25
    @26
    ldualvaddcl
    ldualvadd
    @15
    @22
    @21
    @1
    @18
    co
    @2
    @9
    @18
    co
    #
    @1
    @18
    co
    @20
    @15
    cD
    @17
    @0
    cR
    cF
    @21
    @1
    cW
    clmod
    ldualgrp.f
    ldualgrp.r
    @23
    ldualgrp.d
    @11
    @24
    @15
    cD
    @0
    cF
    @2
    @9
    cW
    ldualgrp.f
    ldualgrp.d
    @11
    @24
    @27
    @25
    ldualvaddcl
    @26
    ldualvadd
    @15
    @21
    @28
    @1
    @18
    @15
    cD
    @17
    @0
    cR
    cF
    @2
    @9
    cW
    clmod
    ldualgrp.f
    ldualgrp.r
    @23
    ldualgrp.d
    @11
    @24
    @27
    @25
    ldualvadd
    oveq1d
    @15
    @17
    cR
    cF
    @2
    @9
    @1
    cW
    ldualgrp.r
    @23
    ldualgrp.f
    @24
    @27
    @25
    @26
    lfladdass
    3eqtrd
    3eqtr4rd
    wph
    @12
    @6
    cF
    wcel
    #
    ldualgrp.w
    cR
    cF
    cV
    cW
    @5
    ldualgrp.r
    @5
    eqid
    #
    ldualgrp.v
    ldualgrp.f
    lfl0f
    syl
    #
    wph
    @8
    wa
    #
    @6
    @2
    @0
    co
    @6
    @2
    @18
    co
    @2
    @32
    cD
    @17
    @0
    cR
    cF
    @6
    @2
    cW
    clmod
    ldualgrp.f
    ldualgrp.r
    @23
    ldualgrp.d
    @11
    wph
    @12
    @8
    ldualgrp.w
    adantr
    #
    wph
    @29
    @8
    @31
    adantr
    wph
    @8
    simpr
    #
    ldualvadd
    @32
    @17
    cR
    cF
    @2
    cV
    cW
    @5
    ldualgrp.v
    ldualgrp.r
    @23
    @30
    ldualgrp.f
    @33
    @34
    lfladd0l
    eqtrd
    @32
    vz
    cR
    cF
    @2
    @3
    @4
    cV
    cW
    ldualgrp.v
    ldualgrp.r
    @3
    eqid
    #
    @4
    eqid
    #
    ldualgrp.f
    @33
    @34
    lflnegcl
    #
    @32
    @4
    @2
    @0
    co
    @4
    @2
    @18
    co
    @6
    @32
    cD
    @17
    @0
    cR
    cF
    @4
    @2
    cW
    clmod
    ldualgrp.f
    ldualgrp.r
    @23
    ldualgrp.d
    @11
    @33
    @37
    @34
    ldualvadd
    @32
    vz
    @17
    cR
    cF
    @2
    @3
    @4
    cV
    cW
    @5
    ldualgrp.v
    ldualgrp.r
    @35
    @36
    ldualgrp.f
    @33
    @34
    @23
    @30
    lflnegl
    eqtrd
    isgrpd
end
