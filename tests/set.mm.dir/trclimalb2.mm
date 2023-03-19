include "wcel.mm"
include "cun.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "ctcl.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "dftrcl3.mm"
include "nnex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "imaeq1d.mm"
include "imaiun1.mm"
include "syl6eq.mm"
include "syl.mm"
include "wral.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "relexp1g.mm"
include "ssun1.mm"
include "imass2.mm"
include "mp1i.mm"
include "simpr.mm"
include "sstrd.mm"
include "eqsstrd.mm"
include "w3a.mm"
include "simp2l.mm"
include "simp1.mm"
include "ccom.mm"
include "relexpsucnnl.mm"
include "imaco.mm"
include "syl2anc.mm"
include "3ad2ant3.mm"
include "ssun2.mm"
include "simp2r.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "com12.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"

theorem trclimalb2
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r


  assert |- ( ( R e. V /\ ( R " ( A u. B ) ) C_ B ) -> ( ( t+ ` R ) " A ) C_ B )

  proof
    cR
    cV
    wcel
    #
    cR
    cA
    cB
    cun
    #
    cima
    #
    cB
    wss
    #
    wa
    #
    cR
    ctcl
    cfv
    #
    cA
    cima
    #
    vk
    cn
    cR
    vk
    cv
    #
    crelexp
    co
    #
    cA
    cima
    #
    ciun
    #
    cB
    @4
    cR
    cvv
    wcel
    #
    @6
    @10
    wceq
    @0
    @11
    @3
    cR
    cV
    elex
    adantr
    @11
    @6
    vk
    cn
    @8
    ciun
    #
    cA
    cima
    @10
    @11
    @5
    @12
    cA
    vr
    cR
    vk
    cn
    vr
    cv
    #
    @7
    crelexp
    co
    #
    ciun
    @12
    cvv
    ctcl
    @13
    cR
    wceq
    vk
    cn
    @14
    @8
    @13
    cR
    @7
    crelexp
    oveq1
    iuneq2d
    vk
    vr
    dftrcl3
    vk
    cn
    @8
    nnex
    cR
    @7
    crelexp
    ovex
    iunex
    fvmpt
    imaeq1d
    vk
    cn
    @8
    cA
    imaiun1
    syl6eq
    syl
    @4
    @9
    cB
    wss
    #
    vk
    cn
    wral
    @10
    cB
    wss
    @4
    @15
    vk
    cn
    @7
    cn
    wcel
    @4
    @15
    @4
    cR
    vx
    cv
    #
    crelexp
    co
    #
    cA
    cima
    #
    cB
    wss
    #
    wi
    @4
    cR
    c1
    crelexp
    co
    #
    cA
    cima
    #
    cB
    wss
    #
    wi
    @4
    cR
    vy
    cv
    #
    crelexp
    co
    #
    cA
    cima
    #
    cB
    wss
    #
    wi
    @4
    cR
    @23
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cA
    cima
    #
    cB
    wss
    #
    wi
    @4
    @15
    wi
    vx
    vy
    @7
    @16
    c1
    wceq
    #
    @19
    @22
    @4
    @31
    @18
    @21
    cB
    @31
    @17
    @20
    cA
    @16
    c1
    cR
    crelexp
    oveq2
    imaeq1d
    sseq1d
    imbi2d
    vx
    vy
    weq
    #
    @19
    @26
    @4
    @32
    @18
    @25
    cB
    @32
    @17
    @24
    cA
    @16
    @23
    cR
    crelexp
    oveq2
    imaeq1d
    sseq1d
    imbi2d
    @16
    @27
    wceq
    #
    @19
    @30
    @4
    @33
    @18
    @29
    cB
    @33
    @17
    @28
    cA
    @16
    @27
    cR
    crelexp
    oveq2
    imaeq1d
    sseq1d
    imbi2d
    vx
    vk
    weq
    #
    @19
    @15
    @4
    @34
    @18
    @9
    cB
    @34
    @17
    @8
    cA
    @16
    @7
    cR
    crelexp
    oveq2
    imaeq1d
    sseq1d
    imbi2d
    @4
    @21
    cR
    cA
    cima
    #
    cB
    @0
    @21
    @35
    wceq
    @3
    @0
    @20
    cR
    cA
    cR
    cV
    relexp1g
    imaeq1d
    adantr
    @4
    @35
    @2
    cB
    cA
    @1
    wss
    @35
    @2
    wss
    @4
    cA
    cB
    ssun1
    cA
    @1
    cR
    imass2
    mp1i
    @0
    @3
    simpr
    sstrd
    eqsstrd
    @23
    cn
    wcel
    #
    @4
    @26
    @30
    @36
    @4
    @26
    @30
    @36
    @4
    @26
    w3a
    #
    @29
    cR
    @25
    cima
    #
    cB
    @37
    @0
    @36
    @29
    @38
    wceq
    @36
    @0
    @3
    @26
    simp2l
    @36
    @4
    @26
    simp1
    @0
    @36
    wa
    #
    @29
    cR
    @24
    ccom
    #
    cA
    cima
    @38
    @39
    @28
    @40
    cA
    cR
    @23
    cV
    relexpsucnnl
    imaeq1d
    cR
    @24
    cA
    imaco
    syl6eq
    syl2anc
    @37
    @38
    cR
    cB
    cima
    #
    cB
    @26
    @36
    @38
    @41
    wss
    @4
    @25
    cB
    cR
    imass2
    3ad2ant3
    @37
    @41
    @2
    cB
    cB
    @1
    wss
    @41
    @2
    wss
    @37
    cB
    cA
    ssun2
    cB
    @1
    cR
    imass2
    mp1i
    @36
    @0
    @3
    @26
    simp2r
    sstrd
    sstrd
    eqsstrd
    3exp
    a2d
    nnind
    com12
    ralrimiv
    vk
    cn
    @9
    cB
    iunss
    sylibr
    eqsstrd
end
