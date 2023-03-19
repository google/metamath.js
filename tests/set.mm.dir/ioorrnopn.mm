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
include "cr.mm"
include "cmap.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "cbl.mm"
include "cfn.mm"
include "ad2antrr.mm"
include "sylan2br.mm"
include "simplr.mm"
include "wf.mm"
include "simpr.mm"
include "eqid.mm"
include "breq12d.mm"
include "ifbieq12d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "infeq1i.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2ad.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "ioorrnopnlem.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "wb.mm"
include "rrxtop.mm"
include "syl.mm"
include "adantr.mm"
include "eltop2.mm"
include "pm2.61dan.mm"

theorem ioorrnopn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume ioorrnopn.x: |- ( ph -> X e. Fin )
  assume ioorrnopn.a: |- ( ph -> A : X --> RR )
  assume ioorrnopn.b: |- ( ph -> B : X --> RR )

  disjoint A i
  disjoint B i
  disjoint X i
  disjoint i ph
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A j
  disjoint A k
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint g h
  disjoint g j
  disjoint g k
  disjoint h j
  disjoint h k
  disjoint j k
  disjoint f i
  disjoint h i
  disjoint i j
  disjoint i k
  disjoint A v
  disjoint f v
  disjoint i v
  disjoint j v
  disjoint k v
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B j
  disjoint B k
  disjoint B v
  disjoint X a
  disjoint X b
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint a b
  disjoint a g
  disjoint a h
  disjoint a k
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint X f
  disjoint X j
  disjoint a i
  disjoint b i
  disjoint X v
  disjoint a v
  disjoint b v
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
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
    va
    vb
    cr
    cX
    cmap
    co
    #
    @30
    cX
    vk
    cv
    #
    va
    cv
    #
    cfv
    #
    @31
    vb
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    #
    vg
    vh
    vi
    vk
    vj
    cX
    @25
    @23
    @18
    cfv
    #
    cmin
    co
    #
    @41
    @24
    cmin
    co
    #
    cle
    wbr
    #
    @42
    @43
    cif
    #
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    @18
    vi
    cX
    @3
    @1
    @18
    cfv
    #
    cmin
    co
    #
    @49
    @2
    cmin
    co
    #
    cle
    wbr
    #
    @50
    @51
    cif
    #
    cmpt
    #
    crn
    #
    @18
    @48
    @40
    cbl
    cfv
    co
    #
    cX
    @28
    @17
    @22
    cX
    cfn
    wcel
    #
    @29
    wph
    @57
    @16
    @22
    ioorrnopn.x
    ad2antrr
    sylan2br
    @28
    @17
    @22
    @16
    @29
    wph
    @16
    @22
    simplr
    sylan2br
    @28
    @17
    @22
    cX
    cr
    cA
    wf
    #
    @29
    wph
    @58
    @16
    @22
    ioorrnopn.a
    ad2antrr
    sylan2br
    @28
    @17
    @22
    cX
    cr
    cB
    wf
    #
    @29
    wph
    @59
    @16
    @22
    ioorrnopn.b
    ad2antrr
    sylan2br
    @28
    @17
    @22
    @22
    @29
    @17
    @22
    simpr
    sylan2br
    @55
    eqid
    cr
    @47
    @55
    clt
    @46
    @54
    vj
    vi
    cX
    @45
    @53
    @23
    @1
    wceq
    #
    @44
    @52
    @42
    @43
    @50
    @51
    @60
    @42
    @50
    @43
    @51
    cle
    @60
    @25
    @3
    @41
    @49
    cmin
    @23
    @1
    cB
    fveq2
    @23
    @1
    @18
    fveq2
    #
    oveq12d
    #
    @60
    @41
    @49
    @24
    @2
    cmin
    @61
    @23
    @1
    cA
    fveq2
    oveq12d
    #
    breq12d
    @62
    @63
    ifbieq12d
    cbvmptv
    rneqi
    infeq1i
    @56
    eqid
    va
    vb
    vg
    vh
    @30
    @30
    @39
    cX
    @31
    vg
    cv
    #
    cfv
    #
    @31
    vh
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    cX
    @65
    @35
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    @32
    @64
    wceq
    #
    @38
    @73
    csqrt
    @74
    cX
    @37
    @72
    vk
    @74
    @36
    @71
    c2
    cexp
    @74
    @33
    @65
    @35
    cmin
    @31
    @32
    @64
    fveq1
    oveq1d
    oveq1d
    sumeq2ad
    fveq2d
    @34
    @66
    wceq
    #
    @73
    @70
    csqrt
    @75
    cX
    @72
    @69
    vk
    @75
    @71
    @68
    c2
    cexp
    @75
    @35
    @67
    @65
    cmin
    @31
    @34
    @66
    fveq1
    oveq2d
    oveq1d
    sumeq2ad
    fveq2d
    cbvmpt2v
    ioorrnopnlem
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
    @76
    @16
    wph
    @57
    @76
    ioorrnopn.x
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
