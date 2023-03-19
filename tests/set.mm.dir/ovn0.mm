include "c0.mm"
include "covoln.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cn.mm"
include "cico.mm"
include "ccom.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "cixp.mm"
include "ciun.mm"
include "wa.mm"
include "wb.mm"
include "wral.mm"
include "id.mm"
include "jca.mm"
include "simpr.mm"
include "impbii.mm"
include "rexbii.mm"
include "rgenw.mm"
include "rabbi.mm"
include "mpbi.mm"
include "ovnval2.mm"
include "iftrued.mm"
include "wn.mm"
include "iffalse.mm"
include "adantl.mm"
include "c1.mm"
include "cop.mm"
include "cfn.mm"
include "wcel.mm"
include "adantr.mm"
include "wne.mm"
include "neqne.mm"
include "eqid.mm"
include "cpnf.mm"
include "cicc.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "cpw.mm"
include "ovnf.mm"
include "0elpw.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "ovn0lem.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"

theorem ovn0
  let wph: wff ph
  let cX: class X
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let vz: setvar z
  let vx: setvar x
  assume ovn0.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( ( voln* ` X ) ` (/) ) = 0 )

  proof
    wph
    c0
    cX
    covoln
    cfv
    #
    cfv
    #
    cX
    c0
    wceq
    #
    cc0
    vz
    cv
    vj
    cn
    cX
    vk
    cv
    cico
    vj
    cv
    #
    vi
    cv
    cfv
    ccom
    cfv
    #
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    wceq
    #
    vi
    cr
    cr
    cxp
    cX
    cmap
    co
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cif
    #
    cc0
    wph
    vz
    c0
    vi
    vj
    vk
    @8
    cX
    ovn0.1
    c0
    cr
    cX
    cmap
    co
    #
    wss
    wph
    @11
    0ss
    a1i
    @7
    c0
    vj
    cn
    vk
    cX
    @4
    cixp
    ciun
    #
    wss
    #
    @5
    wa
    #
    vi
    @6
    wrex
    #
    wb
    #
    vz
    cxr
    wral
    @8
    @15
    vz
    cxr
    crab
    wceq
    @16
    vz
    cxr
    @5
    @14
    vi
    @6
    @5
    @14
    @5
    @13
    @5
    @13
    @5
    @12
    0ss
    a1i
    @5
    id
    jca
    @13
    @5
    simpr
    impbii
    rexbii
    rgenw
    @7
    @15
    vz
    cxr
    rabbi
    mpbi
    ovnval2
    #
    wph
    @2
    @10
    cc0
    wceq
    wph
    @2
    wa
    @2
    cc0
    @9
    wph
    @2
    simpr
    iftrued
    wph
    @2
    wn
    #
    wa
    #
    @10
    @9
    cc0
    @18
    @10
    @9
    wceq
    wph
    @2
    cc0
    @9
    iffalse
    #
    adantl
    @19
    vz
    vi
    vj
    vk
    vh
    cn
    vm
    cX
    c1
    cc0
    cop
    #
    cmpt
    #
    cmpt
    @8
    cX
    vl
    wph
    cX
    cfn
    wcel
    @18
    ovn0.1
    adantr
    @18
    cX
    c0
    wne
    wph
    cX
    c0
    neqne
    adantl
    @8
    eqid
    @19
    @9
    @1
    cc0
    cpnf
    cicc
    co
    #
    @19
    @1
    @9
    wph
    @18
    @1
    @10
    @9
    @17
    @20
    sylan9eq
    eqcomd
    wph
    @1
    @23
    wcel
    @18
    wph
    @11
    cpw
    #
    @23
    c0
    @0
    wph
    cX
    ovn0.1
    ovnf
    c0
    @24
    wcel
    wph
    @11
    0elpw
    a1i
    ffvelrnd
    adantr
    eqeltrd
    vh
    vj
    cn
    @22
    vl
    cX
    @21
    cmpt
    #
    @22
    @25
    wceq
    vh
    cv
    @3
    wceq
    vm
    vl
    cX
    @21
    @21
    vm
    cv
    vl
    cv
    wceq
    @21
    eqidd
    cbvmptv
    a1i
    cbvmptv
    ovn0lem
    eqtrd
    pm2.61dan
    eqtrd
end
