include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cco1.mm"
include "cn.mm"
include "wral.mm"
include "simpl.mm"
include "anim1i.mm"
include "adantr.mm"
include "cply1coe0.mm"
include "syl.mm"
include "wb.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "mpbird.mm"
include "ex.mm"
include "rexlimdva.mm"
include "cc0.mm"
include "cn0.mm"
include "simpr.mm"
include "0nn0.mm"
include "eqid.mm"
include "coe1fvalcl.mm"
include "sylancl.mm"
include "eqeq2d.mm"
include "w3a.mm"
include "csca.mm"
include "cbs.mm"
include "wf.mm"
include "ply1ring.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "3jca.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "coe1scl.mm"
include "syldan.mm"
include "weq.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "eqeq1.mm"
include "notbid.mm"
include "iffalsed.mm"
include "nnnn0.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvmptd.mm"
include "eqtrd.mm"
include "ralimdva.mm"
include "imp.mm"
include "ply1sclid.mm"
include "csn.mm"
include "cun.mm"
include "df-n0.mm"
include "raleqi.mm"
include "c0ex.mm"
include "eqeq12d.mm"
include "ralunsn.mm"
include "mp1i.mm"
include "syl5bb.mm"
include "mpbir2and.mm"
include "eqcoe1ply1eq.mm"
include "sylc.mm"
include "rspcedvd.mm"
include "impbid.mm"

theorem cply1coe0bi
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let vn: setvar n
  let cK: class K
  let cM: class M
  let c.0: class .0.
  let vs: setvar s
  let vk: setvar k
  let cS: class S
  assume cply1coe0.k: |- K = ( Base ` R )
  assume cply1coe0.0: |- .0. = ( 0g ` R )
  assume cply1coe0.p: |- P = ( Poly1 ` R )
  assume cply1coe0.b: |- B = ( Base ` P )
  assume cply1coe0.a: |- A = ( algSc ` P )

  disjoint K n
  disjoint R n
  disjoint A n
  disjoint A s
  disjoint n s
  disjoint B n
  disjoint B s
  disjoint K s
  disjoint M n
  disjoint M s
  disjoint R s
  disjoint .0. s
  disjoint A k
  disjoint K k
  disjoint k n
  disjoint P k
  disjoint R k
  disjoint S k
  disjoint S n
  disjoint .0. k
  disjoint B k
  disjoint M k
  assert |- ( ( R e. Ring /\ M e. B ) -> ( E. s e. K M = ( A ` s ) <-> A. n e. NN ( ( coe1 ` M ) ` n ) = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cM
    vs
    cv
    #
    cA
    cfv
    #
    wceq
    #
    vs
    cK
    wrex
    #
    vn
    cv
    #
    cM
    cco1
    cfv
    #
    cfv
    #
    c.0
    wceq
    #
    vn
    cn
    wral
    #
    @2
    @5
    @11
    vs
    cK
    @2
    @3
    cK
    wcel
    #
    wa
    #
    @5
    @11
    @13
    @5
    wa
    #
    @11
    @7
    @4
    cco1
    cfv
    #
    cfv
    #
    c.0
    wceq
    #
    vn
    cn
    wral
    #
    @14
    @0
    @12
    wa
    #
    @18
    @13
    @19
    @5
    @2
    @0
    @12
    @0
    @1
    simpl
    #
    anim1i
    adantr
    cA
    cB
    cP
    cR
    @3
    vn
    cK
    c.0
    cply1coe0.k
    cply1coe0.0
    cply1coe0.p
    cply1coe0.b
    cply1coe0.a
    cply1coe0
    syl
    @5
    @11
    @18
    wb
    @13
    @5
    @10
    @17
    vn
    cn
    @5
    @9
    @16
    c.0
    @5
    @7
    @8
    @15
    cM
    @4
    cco1
    fveq2
    fveq1d
    eqeq1d
    ralbidv
    adantl
    mpbird
    ex
    rexlimdva
    @2
    @11
    @6
    @2
    @11
    wa
    #
    @5
    cM
    cc0
    @8
    cfv
    #
    cA
    cfv
    #
    wceq
    #
    vs
    @22
    cK
    @2
    @22
    cK
    wcel
    #
    @11
    @2
    @1
    cc0
    cn0
    wcel
    #
    @25
    @0
    @1
    simpr
    #
    0nn0
    @8
    cB
    cP
    cR
    cM
    cK
    cc0
    @8
    eqid
    #
    cply1coe0.b
    cply1coe0.p
    cply1coe0.k
    coe1fvalcl
    sylancl
    #
    adantr
    @3
    @22
    wceq
    #
    @5
    @24
    wb
    @21
    @30
    @4
    @23
    cM
    @3
    @22
    cA
    fveq2
    eqeq2d
    adantl
    @21
    @0
    @1
    @23
    cB
    wcel
    #
    w3a
    #
    @9
    @7
    @23
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cn0
    wral
    #
    @24
    @2
    @32
    @11
    @2
    @0
    @1
    @31
    @20
    @27
    @2
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    cB
    @22
    cA
    @0
    @38
    cB
    cA
    wf
    @1
    @0
    cA
    cB
    @37
    @38
    cP
    cply1coe0.a
    @37
    eqid
    cP
    cR
    cply1coe0.p
    ply1ring
    cP
    cR
    cply1coe0.p
    ply1lmod
    @38
    eqid
    cply1coe0.b
    asclf
    adantr
    @2
    @22
    cR
    cbs
    cfv
    #
    @38
    @2
    @1
    @26
    @22
    @39
    wcel
    @27
    0nn0
    @8
    cB
    cP
    cR
    cM
    @39
    cc0
    @28
    cply1coe0.b
    cply1coe0.p
    @39
    eqid
    coe1fvalcl
    sylancl
    @0
    @38
    @39
    wceq
    @1
    @0
    @37
    cR
    cbs
    @0
    cR
    @37
    cP
    cR
    crg
    cply1coe0.p
    ply1sca
    eqcomd
    fveq2d
    adantr
    eleqtrrd
    ffvelrnd
    3jca
    adantr
    @21
    @36
    @35
    vn
    cn
    wral
    #
    @22
    cc0
    @33
    cfv
    #
    wceq
    #
    @2
    @11
    @40
    @2
    @10
    @35
    vn
    cn
    @2
    @7
    cn
    wcel
    #
    wa
    #
    @10
    @35
    @44
    @10
    wa
    @9
    c.0
    @34
    @44
    @10
    simpr
    @44
    c.0
    @34
    wceq
    @10
    @44
    @34
    c.0
    @44
    vk
    @7
    vk
    cv
    #
    cc0
    wceq
    #
    @22
    c.0
    cif
    #
    c.0
    cn0
    @33
    cvv
    @2
    @33
    vk
    cn0
    @47
    cmpt
    wceq
    #
    @43
    @0
    @1
    @25
    @48
    @29
    vk
    cA
    cP
    cR
    cK
    @22
    c.0
    cply1coe0.p
    cply1coe0.a
    cply1coe0.k
    cply1coe0.0
    coe1scl
    syldan
    adantr
    @44
    vk
    vn
    weq
    #
    wa
    #
    @46
    @22
    c.0
    @50
    @46
    wn
    #
    @7
    cc0
    wceq
    #
    wn
    #
    @44
    @53
    @49
    @43
    @53
    @2
    @43
    @7
    cc0
    @7
    nnne0
    neneqd
    adantl
    adantr
    @49
    @51
    @53
    wb
    @44
    @49
    @46
    @52
    @45
    @7
    cc0
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    @43
    @7
    cn0
    wcel
    @2
    @7
    nnnn0
    adantl
    c.0
    cvv
    wcel
    @44
    c.0
    cR
    c0g
    cfv
    cvv
    cply1coe0.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fvmptd
    eqcomd
    adantr
    eqtrd
    ex
    ralimdva
    imp
    @2
    @42
    @11
    @0
    @1
    @25
    @42
    @29
    cA
    cP
    cR
    cK
    @22
    cply1coe0.p
    cply1coe0.a
    cply1coe0.k
    ply1sclid
    syldan
    adantr
    @36
    @35
    vn
    cn
    cc0
    csn
    cun
    #
    wral
    #
    @21
    @40
    @42
    wa
    #
    @35
    vn
    cn0
    @54
    df-n0
    raleqi
    cc0
    cvv
    wcel
    @55
    @56
    wb
    @21
    c0ex
    @35
    @42
    vn
    cn
    cc0
    cvv
    @52
    @9
    @22
    @34
    @41
    @7
    cc0
    @8
    fveq2
    @7
    cc0
    @33
    fveq2
    eqeq12d
    ralunsn
    mp1i
    syl5bb
    mpbir2and
    @8
    cB
    @33
    cP
    cR
    vn
    cM
    @23
    cply1coe0.p
    cply1coe0.b
    @28
    @33
    eqid
    eqcoe1ply1eq
    sylc
    rspcedvd
    ex
    impbid
end
