include "cicc.mm"
include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "ccncf.mm"
include "wcel.mm"
include "cncff.mm"
include "syl.mm"
include "ffn.mm"
include "cvv.mm"
include "fvex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "fvconst2.mm"
include "adantl.mm"
include "adantr.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "letrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "ffvelrnda.mm"
include "cmin.mm"
include "subcld.mm"
include "cabs.mm"
include "cc0.mm"
include "cmul.mm"
include "simpr.mm"
include "jca.mm"
include "cdv.mm"
include "cdm.mm"
include "cioo.mm"
include "dmeqd.mm"
include "c0.mm"
include "wne.mm"
include "c0ex.mm"
include "snnz.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "0red.mm"
include "fveq1d.mm"
include "sylan9eq.mm"
include "abs00bd.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "dvlip.mm"
include "syldan.mm"
include "recnd.mm"
include "abscld.mm"
include "mul02d.mm"
include "breqtrd.mm"
include "absge0d.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "abs00d.mm"
include "subeq0d.mm"
include "eqtr2d.mm"
include "eqfnfvd.mm"

theorem dveq0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume dveq0.a: |- ( ph -> A e. RR )
  assume dveq0.b: |- ( ph -> B e. RR )
  assume dveq0.c: |- ( ph -> F e. ( ( A [,] B ) -cn-> CC ) )
  assume dveq0.d: |- ( ph -> ( RR _D F ) = ( ( A (,) B ) X. { 0 } ) )


  assert |- ( ph -> F = ( ( A [,] B ) X. { ( F ` A ) } ) )

  proof
    wph
    vx
    cA
    cB
    cicc
    co
    #
    cF
    @0
    cA
    cF
    cfv
    #
    csn
    cxp
    #
    wph
    @0
    cc
    cF
    wf
    #
    cF
    @0
    wfn
    wph
    cF
    @0
    cc
    ccncf
    co
    wcel
    @3
    dveq0.c
    @0
    cc
    cF
    cncff
    syl
    #
    @0
    cc
    cF
    ffn
    syl
    @1
    cvv
    wcel
    @2
    @0
    wfn
    wph
    cA
    cF
    fvex
    #
    @0
    @1
    cvv
    fnconstg
    mp1i
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    @6
    @2
    cfv
    #
    @1
    @6
    cF
    cfv
    #
    @7
    @9
    @1
    wceq
    wph
    @0
    @1
    @6
    @5
    fvconst2
    adantl
    @8
    @1
    @10
    @8
    @0
    cc
    cA
    cF
    wph
    @3
    @7
    @4
    adantr
    @8
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    cA
    @0
    wcel
    #
    @8
    cA
    wph
    cA
    cr
    wcel
    #
    @7
    dveq0.a
    adantr
    #
    rexrd
    @8
    cB
    wph
    cB
    cr
    wcel
    #
    @7
    dveq0.b
    adantr
    #
    rexrd
    @8
    cA
    @6
    cB
    @13
    @8
    @6
    cr
    wcel
    #
    cA
    @6
    cle
    wbr
    #
    @6
    cB
    cle
    wbr
    #
    wph
    @7
    @16
    @17
    @18
    w3a
    #
    wph
    @12
    @14
    @7
    @19
    wb
    dveq0.a
    dveq0.b
    cA
    cB
    @6
    elicc2
    syl2anc
    biimpa
    #
    simp1d
    #
    @15
    @8
    @16
    @17
    @18
    @20
    simp2d
    @8
    @16
    @17
    @18
    @20
    simp3d
    letrd
    cA
    cB
    lbicc2
    syl3anc
    #
    ffvelrnd
    #
    wph
    @0
    cc
    @6
    cF
    @4
    ffvelrnda
    #
    @8
    @1
    @10
    cmin
    co
    #
    @8
    @1
    @10
    @23
    @24
    subcld
    #
    @8
    @25
    cabs
    cfv
    #
    cc0
    wceq
    #
    @27
    cc0
    cle
    wbr
    #
    cc0
    @27
    cle
    wbr
    #
    @8
    @27
    cc0
    cA
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cc0
    cle
    wph
    @7
    @11
    @7
    wa
    @27
    @33
    cle
    wbr
    @8
    @11
    @7
    @22
    wph
    @7
    simpr
    jca
    wph
    vy
    cA
    cB
    cF
    cc0
    cA
    @6
    dveq0.a
    dveq0.b
    dveq0.c
    wph
    cr
    cF
    cdv
    co
    #
    cdm
    cA
    cB
    cioo
    co
    #
    cc0
    csn
    #
    cxp
    #
    cdm
    #
    @35
    wph
    @34
    @37
    dveq0.d
    dmeqd
    @36
    c0
    wne
    @38
    @35
    wceq
    cc0
    c0ex
    snnz
    @35
    @36
    dmxp
    ax-mp
    syl6eq
    wph
    0red
    wph
    vy
    cv
    #
    @35
    wcel
    #
    wa
    #
    @39
    @34
    cfv
    #
    cabs
    cfv
    cc0
    cc0
    cle
    @41
    @42
    wph
    @40
    @42
    @39
    @37
    cfv
    cc0
    wph
    @39
    @34
    @37
    dveq0.d
    fveq1d
    @35
    cc0
    @39
    c0ex
    fvconst2
    sylan9eq
    abs00bd
    0le0
    syl6eqbr
    dvlip
    syldan
    @8
    @32
    @8
    @32
    @8
    @31
    @8
    cA
    @6
    @8
    cA
    @13
    recnd
    @8
    @6
    @21
    recnd
    subcld
    abscld
    recnd
    mul02d
    breqtrd
    @8
    @25
    @26
    absge0d
    @8
    @27
    cr
    wcel
    cc0
    cr
    wcel
    @28
    @29
    @30
    wa
    wb
    @8
    @25
    @26
    abscld
    0re
    @27
    cc0
    letri3
    sylancl
    mpbir2and
    abs00d
    subeq0d
    eqtr2d
    eqfnfvd
end
