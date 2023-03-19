include "cixp.mm"
include "cv.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "cif.mm"
include "ciin.mm"
include "cin.mm"
include "cpt.mm"
include "ccld.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "cldss.mm"
include "syl.mm"
include "ralrimiva.mm"
include "boxriin.mm"
include "ctop.mm"
include "wf.mm"
include "ptuni.mm"
include "syl2anc.mm"
include "ineq1d.mm"
include "pttop.mm"
include "cdif.mm"
include "sseq1.mm"
include "simpl.mm"
include "wn.mm"
include "ssid.mm"
include "a1i.mm"
include "ifbothda.mm"
include "ralimi.mm"
include "ss2ixp.mm"
include "3syl.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "csb.mm"
include "eqcomd.mm"
include "difeq1d.mm"
include "simpr.mm"
include "boxcutc.mm"
include "ixpeq2.mm"
include "fveq2.mm"
include "unieqd.mm"
include "csbeq1a.mm"
include "difeq12d.mm"
include "adantl.mm"
include "ifeq1da.mm"
include "mprg.mm"
include "3eqtrd.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "cldopn.mm"
include "ptopn2.mm"
include "eqeltrd.mm"
include "wb.mm"
include "iscld.mm"
include "mpbir2and.mm"
include "riincld.mm"

theorem ptcld
  let wph: wff ph
  let cA: class A
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume ptcld.a: |- ( ph -> A e. V )
  assume ptcld.f: |- ( ph -> F : A --> Top )
  assume ptcld.c: |- ( ( ph /\ k e. A ) -> C e. ( Clsd ` ( F ` k ) ) )

  disjoint k ph
  disjoint A k
  disjoint F k
  disjoint V k
  disjoint ph x
  disjoint k x
  disjoint A x
  disjoint C x
  disjoint F x
  assert |- ( ph -> X_ k e. A C e. ( Clsd ` ( Xt_ ` F ) ) )

  proof
    wph
    vk
    cA
    cC
    cixp
    #
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    vx
    cA
    vk
    cA
    @1
    vx
    cv
    #
    wceq
    #
    cC
    @3
    cif
    #
    cixp
    #
    ciin
    #
    cin
    #
    cF
    cpt
    cfv
    #
    ccld
    cfv
    #
    wph
    cC
    @3
    wss
    #
    vk
    cA
    wral
    #
    @0
    @10
    wceq
    wph
    @13
    vk
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    cC
    @2
    ccld
    cfv
    #
    wcel
    #
    @13
    ptcld.c
    cC
    @2
    @3
    @3
    eqid
    cldss
    syl
    ralrimiva
    #
    vk
    vx
    cC
    @3
    cA
    boxriin
    syl
    wph
    @10
    @11
    cuni
    #
    @9
    cin
    #
    @12
    wph
    @4
    @19
    @9
    wph
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    @4
    @19
    wceq
    #
    ptcld.a
    ptcld.f
    vk
    cA
    cF
    @11
    cV
    @11
    eqid
    ptuni
    syl2anc
    #
    ineq1d
    wph
    @11
    ctop
    wcel
    #
    @8
    @12
    wcel
    #
    vx
    cA
    wral
    @20
    @12
    wcel
    wph
    @21
    @22
    @25
    ptcld.a
    ptcld.f
    cA
    cF
    cV
    pttop
    syl2anc
    #
    wph
    @26
    vx
    cA
    wph
    @5
    cA
    wcel
    #
    wa
    #
    @26
    @8
    @19
    wss
    #
    @19
    @8
    cdif
    #
    @11
    wcel
    #
    @29
    @8
    @4
    @19
    wph
    @8
    @4
    wss
    #
    @28
    wph
    @14
    @7
    @3
    wss
    #
    vk
    cA
    wral
    @33
    @18
    @13
    @34
    vk
    cA
    @6
    @13
    @3
    @3
    wss
    #
    @34
    @13
    cC
    @3
    cC
    @7
    @3
    sseq1
    @3
    @7
    @3
    sseq1
    @13
    @6
    simpl
    @35
    @13
    @6
    wn
    wa
    @3
    ssid
    a1i
    ifbothda
    ralimi
    vk
    cA
    @7
    @3
    ss2ixp
    3syl
    adantr
    wph
    @23
    @28
    @24
    adantr
    sseqtrd
    @29
    @31
    vk
    cA
    @6
    @5
    cF
    cfv
    #
    cuni
    #
    vk
    @5
    cC
    csb
    #
    cdif
    #
    @3
    cif
    #
    cixp
    #
    @11
    @29
    @31
    @4
    @8
    cdif
    #
    vk
    cA
    @6
    @3
    cC
    cdif
    #
    @3
    cif
    #
    cixp
    #
    @41
    wph
    @31
    @42
    wceq
    @28
    wph
    @19
    @4
    @8
    wph
    @4
    @19
    @24
    eqcomd
    difeq1d
    adantr
    @29
    @28
    @14
    @42
    @45
    wceq
    wph
    @28
    simpr
    wph
    @14
    @28
    @18
    adantr
    cA
    @3
    cC
    vk
    @5
    boxcutc
    syl2anc
    @45
    @41
    wceq
    #
    @29
    @44
    @40
    wceq
    @46
    vk
    cA
    vk
    cA
    @44
    @40
    ixpeq2
    @15
    @6
    @43
    @39
    @3
    @6
    @43
    @39
    wceq
    @15
    @6
    @3
    @37
    cC
    @38
    @6
    @2
    @36
    @1
    @5
    cF
    fveq2
    #
    unieqd
    vk
    @5
    cC
    csbeq1a
    #
    difeq12d
    adantl
    ifeq1da
    mprg
    a1i
    3eqtrd
    @29
    cA
    vk
    cF
    @39
    cV
    @5
    wph
    @21
    @28
    ptcld.a
    adantr
    wph
    @22
    @28
    ptcld.f
    adantr
    @29
    @38
    @36
    ccld
    cfv
    #
    wcel
    #
    @39
    @36
    wcel
    wph
    @50
    vx
    cA
    wph
    @17
    vk
    cA
    wral
    @50
    vx
    cA
    wral
    wph
    @17
    vk
    cA
    ptcld.c
    ralrimiva
    @17
    @50
    vk
    vx
    cA
    @17
    vx
    nfv
    vk
    @38
    @49
    vk
    @5
    cC
    nfcsb1v
    nfel1
    @6
    cC
    @38
    @16
    @49
    @48
    @6
    @2
    @36
    ccld
    @47
    fveq2d
    eleq12d
    cbvral
    sylib
    r19.21bi
    @38
    @36
    @37
    @37
    eqid
    cldopn
    syl
    ptopn2
    eqeltrd
    wph
    @26
    @30
    @32
    wa
    wb
    #
    @28
    wph
    @25
    @51
    @27
    @8
    @11
    @19
    @19
    eqid
    #
    iscld
    syl
    adantr
    mpbir2and
    ralrimiva
    vx
    cA
    @8
    @11
    @19
    @52
    riincld
    syl2anc
    eqeltrd
    eqeltrd
end
