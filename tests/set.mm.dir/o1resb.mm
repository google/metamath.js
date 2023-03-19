include "co1.mm"
include "wcel.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cres.mm"
include "o1res.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmpt3.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "inss1.mm"
include "syl5ss.mm"
include "wf.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elo1mpt.mm"
include "wa.mm"
include "cif.mm"
include "elin.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "wb.mm"
include "ad2antrr.mm"
include "wss.mm"
include "adantr.mm"
include "sselda.mm"
include "elicopnf.mm"
include "baibd.mm"
include "syl2anc.mm"
include "anbi1d.mm"
include "simplrl.mm"
include "maxle.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "imbi1d.mm"
include "syl5bbr.mm"
include "pm5.74da.mm"
include "syl5bb.mm"
include "ralbidv2.mm"
include "simprl.mm"
include "ifcld.mm"
include "simprr.mm"
include "elo12r.mm"
include "3expia.mm"
include "syl22anc.mm"
include "sylbid.mm"
include "rexlimdvva.mm"
include "impbid2.mm"

theorem o1resb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume rlimresb.1: |- ( ph -> F : A --> CC )
  assume rlimresb.2: |- ( ph -> A C_ RR )
  assume rlimresb.3: |- ( ph -> B e. RR )


  assert |- ( ph -> ( F e. O(1) <-> ( F |` ( B [,) +oo ) ) e. O(1) ) )

  proof
    wph
    cF
    co1
    wcel
    #
    cF
    cB
    cpnf
    cico
    co
    #
    cres
    #
    co1
    wcel
    #
    @1
    cF
    o1res
    wph
    @3
    vx
    cA
    @1
    cin
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    co1
    wcel
    #
    @0
    wph
    @2
    @7
    co1
    wph
    @2
    vx
    cA
    @6
    cmpt
    #
    @1
    cres
    @7
    wph
    cF
    @9
    @1
    wph
    vx
    cA
    cc
    cF
    rlimresb.1
    feqmptd
    reseq1d
    vx
    cA
    @1
    @6
    resmpt3
    syl6eq
    eleq1d
    wph
    @8
    vy
    cv
    #
    @5
    cle
    wbr
    #
    @6
    cabs
    cfv
    vz
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    @4
    wral
    #
    vz
    cr
    wrex
    vy
    cr
    wrex
    @0
    wph
    vx
    vy
    @4
    @6
    vz
    wph
    @4
    cA
    cr
    cA
    @1
    inss1
    #
    rlimresb.2
    syl5ss
    wph
    cA
    cc
    cF
    wf
    #
    @5
    cA
    wcel
    #
    @6
    cc
    wcel
    @5
    @4
    wcel
    #
    rlimresb.1
    @4
    cA
    @5
    @16
    sseli
    cA
    cc
    @5
    cF
    ffvelrn
    syl2an
    elo1mpt
    wph
    @15
    @0
    vy
    vz
    cr
    cr
    wph
    @10
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    wa
    #
    wa
    #
    @15
    cB
    @10
    cle
    wbr
    #
    @10
    cB
    cif
    #
    @5
    cle
    wbr
    #
    @13
    wi
    #
    vx
    cA
    wral
    #
    @0
    @23
    @14
    @27
    vx
    @4
    cA
    @19
    @14
    wi
    #
    @18
    @5
    @1
    wcel
    #
    @14
    wi
    #
    wi
    #
    @23
    @18
    @27
    wi
    @29
    @18
    @30
    wa
    #
    @14
    wi
    @32
    @19
    @33
    @14
    @5
    cA
    @1
    elin
    imbi1i
    @18
    @30
    @14
    impexp
    bitri
    @23
    @18
    @31
    @27
    @31
    @30
    @11
    wa
    #
    @13
    wi
    @23
    @18
    wa
    #
    @27
    @30
    @11
    @13
    impexp
    @35
    @34
    @26
    @13
    @35
    @34
    cB
    @5
    cle
    wbr
    #
    @11
    wa
    #
    @26
    @35
    @30
    @36
    @11
    @35
    cB
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @30
    @36
    wb
    wph
    @38
    @22
    @18
    rlimresb.3
    ad2antrr
    #
    @23
    cA
    cr
    @5
    wph
    cA
    cr
    wss
    #
    @22
    rlimresb.2
    adantr
    #
    sselda
    #
    @38
    @30
    @39
    @36
    cB
    @5
    elicopnf
    baibd
    syl2anc
    anbi1d
    @35
    @38
    @20
    @39
    @26
    @37
    wb
    @40
    wph
    @20
    @21
    @18
    simplrl
    @43
    cB
    @10
    @5
    maxle
    syl3anc
    bitr4d
    imbi1d
    syl5bbr
    pm5.74da
    syl5bb
    ralbidv2
    @23
    @17
    @41
    @25
    cr
    wcel
    #
    @21
    @28
    @0
    wi
    wph
    @17
    @22
    rlimresb.1
    adantr
    @42
    @23
    @24
    @10
    cB
    cr
    wph
    @20
    @21
    simprl
    wph
    @38
    @22
    rlimresb.3
    adantr
    ifcld
    wph
    @20
    @21
    simprr
    @17
    @41
    wa
    @44
    @21
    wa
    @28
    @0
    vx
    cA
    @25
    cF
    @12
    elo12r
    3expia
    syl22anc
    sylbid
    rexlimdvva
    sylbid
    sylbid
    impbid2
end
