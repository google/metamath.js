include "cv.mm"
include "cslw.mm"
include "co.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cpc.mm"
include "cexp.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cgrp.mm"
include "cfn.mm"
include "cprime.mm"
include "slwn0.mm"
include "syl3anc.mm"
include "n0.mm"
include "sylib.mm"
include "cplusg.mm"
include "csg.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "crab.mm"
include "wb.mm"
include "wral.mm"
include "adantr.mm"
include "eqid.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "mpteq1.mm"
include "cbvmpt2v.mm"
include "simpr.mm"
include "sylow3lem4.mm"
include "syl5eqbr.mm"
include "oveq1i.mm"
include "sylow3lem6.mm"
include "jca.mm"
include "exlimddv.mm"

theorem sylow3
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.mi: class .-
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let c.po: class .(+)
  let cH: class H
  let cK: class K
  let vk: setvar k
  let c.pl: class .+
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3.n: |- N = ( # ` ( P pSyl G ) )


  assert |- ( ph -> ( N || ( ( # ` X ) / ( P ^ ( P pCnt ( # ` X ) ) ) ) /\ ( N mod P ) = 1 ) )

  proof
    wph
    vk
    cv
    #
    cP
    cG
    cslw
    co
    #
    wcel
    #
    cN
    cX
    chash
    cfv
    #
    cP
    cP
    @3
    cpc
    co
    cexp
    co
    cdiv
    co
    #
    cdvds
    wbr
    #
    cN
    cP
    cmo
    co
    #
    c1
    wceq
    #
    wa
    vk
    wph
    @1
    c0
    wne
    #
    @2
    vk
    wex
    wph
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    cP
    cprime
    wcel
    #
    @8
    sylow3.g
    sylow3.xf
    sylow3.p
    cP
    cG
    cX
    sylow3.x
    slwn0
    syl3anc
    vk
    @1
    n0
    sylib
    wph
    @2
    wa
    #
    @5
    @7
    @12
    cN
    @1
    chash
    cfv
    #
    @4
    cdvds
    sylow3.n
    @12
    vx
    vy
    vz
    vu
    cP
    cG
    cplusg
    cfv
    #
    va
    vb
    cX
    @1
    vc
    vb
    cv
    #
    va
    cv
    #
    vc
    cv
    #
    @14
    co
    #
    @16
    cG
    csg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    #
    cG
    vu
    cv
    @0
    @23
    co
    @0
    wceq
    vu
    cX
    crab
    #
    @0
    @19
    vx
    cv
    #
    vy
    cv
    #
    @14
    co
    #
    @0
    wcel
    @26
    @25
    @14
    co
    #
    @0
    wcel
    wb
    vy
    cX
    wral
    vx
    cX
    crab
    #
    cX
    sylow3.x
    wph
    @9
    @2
    sylow3.g
    adantr
    #
    wph
    @10
    @2
    sylow3.xf
    adantr
    #
    wph
    @11
    @2
    sylow3.p
    adantr
    #
    @14
    eqid
    #
    @19
    eqid
    #
    va
    vb
    vx
    vy
    cX
    @1
    @22
    vz
    @26
    @25
    vz
    cv
    #
    @14
    co
    #
    @25
    @19
    co
    #
    cmpt
    #
    crn
    #
    vz
    @15
    @37
    cmpt
    #
    crn
    #
    @16
    @25
    wceq
    #
    @21
    @40
    @42
    @21
    vz
    @15
    @16
    @35
    @14
    co
    #
    @16
    @19
    co
    #
    cmpt
    @40
    vc
    vz
    @15
    @20
    @44
    @17
    @35
    wceq
    @18
    @43
    @16
    @19
    @17
    @35
    @16
    @14
    oveq2
    oveq1d
    cbvmptv
    @42
    vz
    @15
    @44
    @37
    @42
    @43
    @36
    @16
    @25
    @19
    @16
    @25
    @35
    @14
    oveq1
    @42
    id
    oveq12d
    mpteq2dv
    syl5eq
    rneqd
    #
    @15
    @26
    wceq
    @40
    @38
    vz
    @15
    @26
    @37
    mpteq1
    rneqd
    #
    cbvmpt2v
    wph
    @2
    simpr
    #
    @24
    eqid
    @29
    eqid
    sylow3lem4
    syl5eqbr
    @12
    @6
    @13
    cP
    cmo
    co
    c1
    cN
    @13
    cP
    cmo
    sylow3.n
    oveq1i
    @12
    vx
    vy
    vz
    cP
    @14
    va
    vb
    @0
    @1
    @22
    cmpt2
    cG
    @0
    @19
    @27
    vs
    cv
    #
    wcel
    @28
    @48
    wcel
    wb
    vy
    cX
    wral
    vx
    cX
    crab
    #
    cX
    vs
    sylow3.x
    @30
    @31
    @32
    @33
    @34
    @47
    va
    vb
    vx
    vy
    @0
    @1
    @22
    @39
    @41
    @45
    @46
    cbvmpt2v
    @49
    eqid
    sylow3lem6
    syl5eq
    jca
    exlimddv
end
