include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cplusg.mm"
include "cv.mm"
include "cixp.mm"
include "cmgp.mm"
include "ccom.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "mgpbas.mm"
include "wfn.mm"
include "fvco2.mm"
include "sylan.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "ixpeq2dva.mm"
include "eqcomi.mm"
include "prdsbas2.mm"
include "cvv.mm"
include "crn.mm"
include "wss.mm"
include "fnmgp.mm"
include "a1i.mm"
include "ssv.mm"
include "fnco.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"
include "cmulr.mm"
include "mgpplusg.mm"
include "co.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "oveqd.mm"
include "mpteq2dva.mm"
include "mpt2eq123dv.mm"
include "fnex.mm"
include "syl2anc.mm"
include "cdm.mm"
include "fndm.mm"
include "syl.mm"
include "prdsmulr.mm"
include "prdsplusg.mm"
include "syl5eqr.mm"
include "jca.mm"

theorem prdsmgp
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cM: class M
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume prdsmgp.y: |- Y = ( S Xs_ R )
  assume prdsmgp.m: |- M = ( mulGrp ` Y )
  assume prdsmgp.z: |- Z = ( S Xs_ ( mulGrp o. R ) )
  assume prdsmgp.i: |- ( ph -> I e. V )
  assume prdsmgp.s: |- ( ph -> S e. W )
  assume prdsmgp.r: |- ( ph -> R Fn I )


  assert |- ( ph -> ( ( Base ` M ) = ( Base ` Z ) /\ ( +g ` M ) = ( +g ` Z ) ) )

  proof
    wph
    cM
    cbs
    cfv
    #
    cZ
    cbs
    cfv
    #
    wceq
    cM
    cplusg
    cfv
    #
    cZ
    cplusg
    cfv
    #
    wceq
    wph
    vx
    cI
    vx
    cv
    #
    cR
    cfv
    #
    cbs
    cfv
    #
    cixp
    vx
    cI
    @4
    cmgp
    cR
    ccom
    #
    cfv
    #
    cbs
    cfv
    #
    cixp
    @0
    @1
    wph
    vx
    cI
    @6
    @9
    wph
    @4
    cI
    wcel
    #
    wa
    #
    @6
    @5
    cmgp
    cfv
    #
    cbs
    cfv
    @9
    @6
    @5
    @12
    @12
    eqid
    @6
    eqid
    mgpbas
    @11
    @12
    @8
    cbs
    @11
    @8
    @12
    wph
    cR
    cI
    wfn
    #
    @10
    @8
    @12
    wceq
    prdsmgp.r
    cI
    cmgp
    cR
    @4
    fvco2
    sylan
    eqcomd
    fveq2d
    syl5eq
    ixpeq2dva
    wph
    vx
    @0
    cR
    cS
    cI
    cW
    cV
    cY
    prdsmgp.y
    cY
    cbs
    cfv
    #
    @0
    @14
    cY
    cM
    prdsmgp.m
    @14
    eqid
    mgpbas
    eqcomi
    #
    prdsmgp.s
    prdsmgp.i
    prdsmgp.r
    prdsbas2
    wph
    vx
    @1
    @7
    cS
    cI
    cW
    cV
    cZ
    prdsmgp.z
    @1
    eqid
    #
    prdsmgp.s
    prdsmgp.i
    wph
    cmgp
    cvv
    wfn
    #
    @13
    cR
    crn
    #
    cvv
    wss
    #
    @7
    cI
    wfn
    #
    @17
    wph
    fnmgp
    a1i
    prdsmgp.r
    @19
    wph
    @18
    ssv
    a1i
    cvv
    cI
    cmgp
    cR
    fnco
    syl3anc
    #
    prdsbas2
    3eqtr4d
    #
    wph
    @2
    cY
    cmulr
    cfv
    #
    @3
    cY
    @23
    cM
    prdsmgp.m
    @23
    eqid
    #
    mgpplusg
    wph
    vx
    vy
    @0
    @0
    vz
    cI
    vz
    cv
    #
    @4
    cfv
    #
    @25
    vy
    cv
    cfv
    #
    @25
    cR
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    vx
    vy
    @1
    @1
    vz
    cI
    @26
    @27
    @25
    @7
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    @23
    @3
    wph
    vx
    vy
    @0
    @0
    @31
    @1
    @1
    @35
    @22
    @22
    wph
    vz
    cI
    @30
    @34
    wph
    @25
    cI
    wcel
    #
    wa
    #
    @29
    @33
    @26
    @27
    @37
    @29
    @28
    cmgp
    cfv
    #
    cplusg
    cfv
    @33
    @28
    @29
    @38
    @38
    eqid
    @29
    eqid
    mgpplusg
    @37
    @38
    @32
    cplusg
    @37
    @32
    @38
    wph
    @13
    @36
    @32
    @38
    wceq
    prdsmgp.r
    cI
    cmgp
    cR
    @25
    fvco2
    sylan
    eqcomd
    fveq2d
    syl5eq
    oveqd
    mpteq2dva
    mpt2eq123dv
    wph
    vz
    @0
    cY
    cR
    cS
    @23
    vx
    vy
    cI
    cW
    cvv
    prdsmgp.y
    prdsmgp.s
    wph
    @13
    cI
    cV
    wcel
    #
    cR
    cvv
    wcel
    prdsmgp.r
    prdsmgp.i
    cI
    cV
    cR
    fnex
    syl2anc
    @15
    wph
    @13
    cR
    cdm
    cI
    wceq
    prdsmgp.r
    cI
    cR
    fndm
    syl
    @24
    prdsmulr
    wph
    vz
    @1
    cZ
    @3
    @7
    cS
    vx
    vy
    cI
    cW
    cvv
    prdsmgp.z
    prdsmgp.s
    wph
    @20
    @39
    @7
    cvv
    wcel
    @21
    prdsmgp.i
    cI
    cV
    @7
    fnex
    syl2anc
    @16
    wph
    @20
    @7
    cdm
    cI
    wceq
    @21
    cI
    @7
    fndm
    syl
    @3
    eqid
    prdsplusg
    3eqtr4d
    syl5eqr
    jca
end
