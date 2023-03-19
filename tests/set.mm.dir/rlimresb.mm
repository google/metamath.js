include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cres.mm"
include "cc.mm"
include "wcel.mm"
include "wi.mm"
include "rlimcl.mm"
include "a1i.mm"
include "wb.mm"
include "wa.mm"
include "cle.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cr.mm"
include "wss.mm"
include "adantr.mm"
include "simprrl.mm"
include "sseldd.mm"
include "elicopnf.mm"
include "syl.mm"
include "biimpa.mm"
include "adantrr.mm"
include "simpld.mm"
include "simprd.mm"
include "simprrr.mm"
include "letrd.mm"
include "mpbir2and.mm"
include "anassrs.mm"
include "biimt.mm"
include "pm5.74da.mm"
include "bi2.04.mm"
include "syl6bb.mm"
include "elin.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "ralbidv2.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "simpr.mm"
include "rlim3.mm"
include "inss1.mm"
include "sseli.mm"
include "sylan2.mm"
include "syl5ss.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "feqmptd.mm"
include "breq1d.mm"
include "resres.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "3eqtr3a.mm"

theorem rlimresb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rlimresb.1: |- ( ph -> F : A --> CC )
  assume rlimresb.2: |- ( ph -> A C_ RR )
  assume rlimresb.3: |- ( ph -> B e. RR )


  assert |- ( ph -> ( F ~~>r C <-> ( F |` ( B [,) +oo ) ) ~~>r C ) )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cC
    crli
    wbr
    #
    vx
    cA
    cB
    cpnf
    cico
    co
    #
    cin
    #
    @1
    cmpt
    #
    cC
    crli
    wbr
    #
    cF
    cC
    crli
    wbr
    cF
    @4
    cres
    #
    cC
    crli
    wbr
    wph
    cC
    cc
    wcel
    #
    @3
    @7
    @3
    @9
    wi
    wph
    cC
    @2
    rlimcl
    a1i
    @7
    @9
    wi
    wph
    cC
    @6
    rlimcl
    a1i
    wph
    @9
    @3
    @7
    wb
    wph
    @9
    wa
    #
    vz
    cv
    #
    @0
    cle
    wbr
    #
    @1
    cC
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    @4
    wrex
    #
    vy
    crp
    wral
    #
    @14
    vx
    @5
    wral
    #
    vz
    @4
    wrex
    #
    vy
    crp
    wral
    #
    @3
    @7
    wph
    @17
    @20
    wb
    @9
    wph
    @16
    @19
    vy
    crp
    wph
    @15
    @18
    vz
    @4
    wph
    @11
    @4
    wcel
    #
    wa
    #
    @14
    @14
    vx
    cA
    @5
    @22
    @0
    cA
    wcel
    #
    @14
    wi
    @23
    @0
    @4
    wcel
    #
    @14
    wi
    #
    wi
    #
    @0
    @5
    wcel
    #
    @14
    wi
    #
    @22
    @23
    @14
    @25
    @22
    @23
    wa
    #
    @14
    @12
    @24
    @13
    wi
    #
    wi
    @25
    @29
    @12
    @13
    @30
    @29
    @12
    wa
    @24
    @13
    @30
    wb
    @22
    @23
    @12
    @24
    wph
    @21
    @23
    @12
    wa
    #
    @24
    wph
    @21
    @31
    wa
    #
    wa
    #
    @24
    @0
    cr
    wcel
    #
    cB
    @0
    cle
    wbr
    #
    @33
    cA
    cr
    @0
    wph
    cA
    cr
    wss
    #
    @32
    rlimresb.2
    adantr
    wph
    @21
    @23
    @12
    simprrl
    sseldd
    #
    @33
    cB
    @11
    @0
    wph
    cB
    cr
    wcel
    #
    @32
    rlimresb.3
    adantr
    #
    @33
    @11
    cr
    wcel
    #
    cB
    @11
    cle
    wbr
    #
    wph
    @21
    @40
    @41
    wa
    #
    @31
    wph
    @21
    @42
    wph
    @38
    @21
    @42
    wb
    rlimresb.3
    cB
    @11
    elicopnf
    syl
    biimpa
    adantrr
    #
    simpld
    @37
    @33
    @40
    @41
    @43
    simprd
    wph
    @21
    @23
    @12
    simprrr
    letrd
    @33
    @38
    @24
    @34
    @35
    wa
    wb
    @39
    cB
    @0
    elicopnf
    syl
    mpbir2and
    anassrs
    anassrs
    @24
    @13
    biimt
    syl
    pm5.74da
    @12
    @24
    @13
    bi2.04
    syl6bb
    pm5.74da
    @28
    @23
    @24
    wa
    #
    @14
    wi
    @26
    @27
    @44
    @14
    @0
    cA
    @4
    elin
    imbi1i
    @23
    @24
    @14
    impexp
    bitri
    syl6bbr
    ralbidv2
    rexbidva
    ralbidv
    adantr
    @10
    vy
    vz
    vx
    cA
    @1
    cC
    cB
    wph
    @1
    cc
    wcel
    #
    vx
    cA
    wral
    @9
    wph
    @45
    vx
    cA
    wph
    cA
    cc
    @0
    cF
    rlimresb.1
    ffvelrnda
    #
    ralrimiva
    adantr
    wph
    @36
    @9
    rlimresb.2
    adantr
    wph
    @9
    simpr
    #
    wph
    @38
    @9
    rlimresb.3
    adantr
    #
    rlim3
    @10
    vy
    vz
    vx
    @5
    @1
    cC
    cB
    wph
    @45
    vx
    @5
    wral
    @9
    wph
    @45
    vx
    @5
    @27
    wph
    @23
    @45
    @5
    cA
    @0
    cA
    @4
    inss1
    #
    sseli
    @46
    sylan2
    ralrimiva
    adantr
    wph
    @5
    cr
    wss
    @9
    wph
    @5
    cA
    cr
    @49
    rlimresb.2
    syl5ss
    adantr
    @47
    @48
    rlim3
    3bitr4d
    ex
    pm5.21ndd
    wph
    cF
    @2
    cC
    crli
    wph
    vx
    cA
    cc
    cF
    rlimresb.1
    feqmptd
    #
    breq1d
    wph
    @8
    @6
    cC
    crli
    wph
    cF
    cA
    cres
    #
    @4
    cres
    cF
    @5
    cres
    #
    @8
    @6
    cF
    cA
    @4
    resres
    wph
    @51
    cF
    @4
    wph
    cA
    cc
    cF
    wf
    cF
    cA
    wfn
    @51
    cF
    wceq
    rlimresb.1
    cA
    cc
    cF
    ffn
    cA
    cF
    fnresdm
    3syl
    reseq1d
    wph
    @52
    @2
    @5
    cres
    #
    @6
    wph
    cF
    @2
    @5
    @50
    reseq1d
    @5
    cA
    wss
    @53
    @6
    wceq
    @49
    vx
    cA
    @5
    @1
    resmpt
    ax-mp
    syl6eq
    3eqtr3a
    breq1d
    3bitr4d
end
