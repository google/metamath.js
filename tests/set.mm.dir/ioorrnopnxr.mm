include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cioo.mm"
include "co.mm"
include "cixp.mm"
include "crrx.mm"
include "ctopn.mm"
include "wcel.mm"
include "csn.mm"
include "cpr.mm"
include "p0ex.mm"
include "prid2.mm"
include "a1i.mm"
include "ixpeq1.mm"
include "ixp0x.mm"
include "eqtrd.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "rrxtopn0b.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "adantl.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "wa.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "oveq12d.mm"
include "cbvixpv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cpnf.mm"
include "c1.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt.mm"
include "cmnf.mm"
include "cmin.mm"
include "cfn.mm"
include "ad2antrr.mm"
include "cxr.mm"
include "wf.mm"
include "biimpri.mm"
include "eqeq1d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "ioorrnopnxrlem.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "wb.mm"
include "rrxtop.mm"
include "syl.mm"
include "adantr.mm"
include "eltop2.mm"
include "pm2.61dan.mm"

theorem ioorrnopnxr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cX: class X
  let vf: setvar f
  let vj: setvar j
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume ioorrnopnxr.x: |- ( ph -> X e. Fin )
  assume ioorrnopnxr.a: |- ( ph -> A : X --> RR* )
  assume ioorrnopnxr.b: |- ( ph -> B : X --> RR* )

  disjoint A i
  disjoint B i
  disjoint X i
  disjoint i ph
  disjoint A f
  disjoint A j
  disjoint A v
  disjoint f i
  disjoint f j
  disjoint f v
  disjoint i j
  disjoint i v
  disjoint j v
  disjoint B f
  disjoint B j
  disjoint B v
  disjoint X f
  disjoint X j
  disjoint X v
  disjoint f ph
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) (,) ( B ` i ) ) e. ( TopOpen ` ( RR^ ` X ) ) )

  proof
    wph
    cX
    c0
    wceq
    #
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @1
    cB
    cfv
    #
    cioo
    co
    #
    cixp
    #
    cX
    crrx
    cfv
    #
    ctopn
    cfv
    #
    wcel
    #
    @0
    @8
    wph
    @0
    @8
    c0
    csn
    #
    c0
    @9
    cpr
    #
    wcel
    #
    @11
    @0
    c0
    @9
    p0ex
    prid2
    a1i
    @0
    @5
    @9
    @7
    @10
    @0
    @5
    vi
    c0
    @4
    cixp
    #
    @9
    vi
    cX
    c0
    @4
    ixpeq1
    @12
    @9
    wceq
    @0
    vi
    @4
    ixp0x
    a1i
    eqtrd
    @0
    @7
    c0
    crrx
    cfv
    #
    ctopn
    cfv
    #
    @10
    @0
    @6
    @13
    ctopn
    cX
    c0
    crrx
    fveq2
    fveq2d
    @14
    @10
    wceq
    @0
    rrxtopn0b
    a1i
    eqtrd
    eleq12d
    mpbird
    adantl
    wph
    @0
    wn
    #
    cX
    c0
    wne
    #
    @8
    @15
    @16
    wph
    cX
    c0
    neqne
    adantl
    wph
    @16
    wa
    #
    @8
    vf
    cv
    #
    vv
    cv
    #
    wcel
    @19
    @5
    wss
    wa
    vv
    @7
    wrex
    #
    vf
    @5
    wral
    #
    @17
    @20
    vf
    @5
    @17
    @18
    @5
    wcel
    #
    @18
    vj
    cX
    vj
    cv
    #
    cA
    cfv
    #
    @23
    cB
    cfv
    #
    cioo
    co
    #
    cixp
    #
    wcel
    #
    @20
    @22
    @28
    @17
    @22
    @28
    @5
    @27
    @18
    vi
    vj
    cX
    @4
    @26
    @1
    @23
    wceq
    @2
    @24
    @3
    @25
    cioo
    @1
    @23
    cA
    fveq2
    @1
    @23
    cB
    fveq2
    oveq12d
    cbvixpv
    eleq2i
    #
    biimpi
    adantl
    @17
    @28
    wa
    vv
    cA
    cB
    vj
    cX
    @25
    cpnf
    wceq
    #
    @23
    @18
    cfv
    #
    c1
    caddc
    co
    #
    @25
    cif
    #
    cmpt
    #
    vi
    @18
    vj
    cX
    @24
    cmnf
    wceq
    #
    @31
    c1
    cmin
    co
    #
    @24
    cif
    #
    cmpt
    #
    vi
    cX
    @1
    @38
    cfv
    @1
    @34
    cfv
    cioo
    co
    cixp
    #
    cX
    wph
    cX
    cfn
    wcel
    #
    @16
    @28
    ioorrnopnxr.x
    ad2antrr
    wph
    cX
    cxr
    cA
    wf
    @16
    @28
    ioorrnopnxr.a
    ad2antrr
    wph
    cX
    cxr
    cB
    wf
    @16
    @28
    ioorrnopnxr.b
    ad2antrr
    @28
    @22
    @17
    @22
    @28
    @29
    biimpri
    adantl
    vj
    vi
    cX
    @37
    @2
    cmnf
    wceq
    #
    @1
    @18
    cfv
    #
    c1
    cmin
    co
    #
    @2
    cif
    @23
    @1
    wceq
    #
    @35
    @41
    @36
    @24
    @43
    @2
    @44
    @24
    @2
    cmnf
    @23
    @1
    cA
    fveq2
    #
    eqeq1d
    @44
    @31
    @42
    c1
    cmin
    @23
    @1
    @18
    fveq2
    #
    oveq1d
    @45
    ifbieq12d
    cbvmptv
    vj
    vi
    cX
    @33
    @3
    cpnf
    wceq
    #
    @42
    c1
    caddc
    co
    #
    @3
    cif
    @44
    @30
    @47
    @32
    @25
    @48
    @3
    @44
    @25
    @3
    cpnf
    @23
    @1
    cB
    fveq2
    #
    eqeq1d
    @44
    @31
    @42
    c1
    caddc
    @46
    oveq1d
    @49
    ifbieq12d
    cbvmptv
    @39
    eqid
    ioorrnopnxrlem
    syldan
    ralrimiva
    @17
    @7
    ctop
    wcel
    #
    @8
    @21
    wb
    wph
    @50
    @16
    wph
    @40
    @50
    ioorrnopnxr.x
    cX
    @7
    cfn
    @7
    eqid
    rrxtop
    syl
    adantr
    vf
    vv
    @5
    @7
    eltop2
    syl
    mpbird
    syldan
    pm2.61dan
end
