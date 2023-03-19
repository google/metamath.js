include "cplusg.mm"
include "cfv.mm"
include "csca.mm"
include "cmulr.mm"
include "cur.mm"
include "cbs.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualvbase.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "ldualsca.mm"
include "cvsca.mm"
include "wceq.mm"
include "a1i.mm"
include "opprbas.mm"
include "oppradd.mm"
include "fveq2d.mm"
include "oppr1.mm"
include "wcel.mm"
include "crg.mm"
include "lmodring.mm"
include "opprring.mm"
include "3syl.mm"
include "ldualgrp.mm"
include "cv.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "ldualvscl.mm"
include "wa.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ldualvsdi1.mm"
include "ldualvsdi2.mm"
include "ldualvsass2.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "ringidcl.mm"
include "simpr.mm"
include "ldualvs.mm"
include "lfl1sc.mm"
include "eqtrd.mm"
include "islmodd.mm"

theorem lduallmodlem
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
  assume lduallmod.d: |- D = ( LDual ` W )
  assume lduallmod.w: |- ( ph -> W e. LMod )
  assume lduallmod.v: |- V = ( Base ` W )
  assume lduallmod.p: |- .+ = oF ( +g ` W )
  assume lduallmod.f: |- F = ( LFnl ` W )
  assume lduallmod.r: |- R = ( Scalar ` W )
  assume lduallmod.k: |- K = ( Base ` R )
  assume lduallmod.t: |- .X. = ( .r ` R )
  assume lduallmod.o: |- O = ( oppR ` R )
  assume lduallmod.s: |- .x. = ( .s ` D )


  assert |- ( ph -> D e. LMod )

  proof
    wph
    vx
    vy
    vz
    cK
    cD
    cplusg
    cfv
    #
    cR
    cplusg
    cfv
    #
    c.x
    cD
    csca
    cfv
    #
    cmulr
    cfv
    #
    cR
    cur
    cfv
    #
    cO
    cF
    cD
    wph
    cD
    cbs
    cfv
    #
    cF
    wph
    cD
    cF
    @5
    cW
    clmod
    lduallmod.f
    lduallmod.d
    @5
    eqid
    lduallmod.w
    ldualvbase
    eqcomd
    wph
    @0
    eqidd
    wph
    @2
    cO
    wph
    cD
    @2
    cR
    cO
    cW
    clmod
    lduallmod.r
    lduallmod.o
    lduallmod.d
    @2
    eqid
    #
    lduallmod.w
    ldualsca
    #
    eqcomd
    c.x
    cD
    cvsca
    cfv
    wceq
    wph
    lduallmod.s
    a1i
    cK
    cO
    cbs
    cfv
    wceq
    wph
    cK
    cR
    cO
    lduallmod.o
    lduallmod.k
    opprbas
    a1i
    @1
    cO
    cplusg
    cfv
    wceq
    wph
    @1
    cR
    cO
    lduallmod.o
    @1
    eqid
    #
    oppradd
    a1i
    wph
    @2
    cO
    cmulr
    @7
    fveq2d
    @4
    cO
    cur
    cfv
    wceq
    wph
    cR
    @4
    cO
    lduallmod.o
    @4
    eqid
    #
    oppr1
    a1i
    wph
    cW
    clmod
    wcel
    #
    cR
    crg
    wcel
    #
    cO
    crg
    wcel
    lduallmod.w
    cR
    cW
    lduallmod.r
    lmodring
    #
    cR
    cO
    lduallmod.o
    opprring
    3syl
    wph
    cD
    cW
    lduallmod.d
    lduallmod.w
    ldualgrp
    wph
    vx
    cv
    #
    cK
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
    cR
    c.x
    cF
    @15
    cK
    cW
    @13
    lduallmod.f
    lduallmod.r
    lduallmod.k
    lduallmod.d
    lduallmod.s
    wph
    @14
    @10
    @16
    lduallmod.w
    3ad2ant1
    wph
    @14
    @16
    simp2
    wph
    @14
    @16
    simp3
    ldualvscl
    wph
    @14
    @16
    vz
    cv
    #
    cF
    wcel
    #
    w3a
    #
    wa
    cD
    @0
    cR
    c.x
    cF
    @15
    @17
    cK
    cW
    @13
    lduallmod.f
    lduallmod.r
    lduallmod.k
    lduallmod.d
    @0
    eqid
    #
    lduallmod.s
    wph
    @10
    @19
    lduallmod.w
    adantr
    wph
    @14
    @16
    @18
    simpr1
    wph
    @14
    @16
    @18
    simpr2
    wph
    @14
    @16
    @18
    simpr3
    ldualvsdi1
    wph
    @14
    @15
    cK
    wcel
    #
    @18
    w3a
    #
    wa
    #
    cD
    @1
    @0
    cR
    c.x
    cF
    @17
    cK
    cW
    @13
    @15
    lduallmod.f
    lduallmod.r
    @8
    lduallmod.k
    lduallmod.d
    @20
    lduallmod.s
    wph
    @10
    @22
    lduallmod.w
    adantr
    #
    wph
    @14
    @21
    @18
    simpr1
    #
    wph
    @14
    @21
    @18
    simpr2
    #
    wph
    @14
    @21
    @18
    simpr3
    #
    ldualvsdi2
    @23
    cD
    @2
    cR
    c.x
    @3
    cF
    @17
    cK
    cW
    @13
    @15
    lduallmod.f
    lduallmod.r
    lduallmod.k
    lduallmod.d
    @6
    @3
    eqid
    lduallmod.s
    @24
    @25
    @26
    @27
    ldualvsass2
    wph
    @13
    cF
    wcel
    #
    wa
    #
    @4
    @13
    c.x
    co
    @13
    cV
    @4
    csn
    cxp
    c.xp
    cof
    co
    @13
    @29
    cD
    cR
    c.x
    c.xp
    cF
    @13
    cK
    cV
    cW
    @4
    clmod
    lduallmod.f
    lduallmod.v
    lduallmod.r
    lduallmod.k
    lduallmod.t
    lduallmod.d
    lduallmod.s
    wph
    @10
    @28
    lduallmod.w
    adantr
    #
    wph
    @4
    cK
    wcel
    #
    @28
    wph
    @10
    @11
    @31
    lduallmod.w
    @12
    cK
    cR
    @4
    lduallmod.k
    @9
    ringidcl
    3syl
    adantr
    wph
    @28
    simpr
    #
    ldualvs
    @29
    cR
    c.xp
    @4
    cF
    @13
    cK
    cV
    cW
    lduallmod.v
    lduallmod.r
    lduallmod.f
    lduallmod.k
    lduallmod.t
    @9
    @30
    @32
    lfl1sc
    eqtrd
    islmodd
end
