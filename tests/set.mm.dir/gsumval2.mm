include "crn.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "cgsu.mm"
include "cseq.mm"
include "cfv.mm"
include "c0g.mm"
include "cfz.mm"
include "cvv.mm"
include "eqid.mm"
include "wcel.mm"
include "adantr.mm"
include "ovexd.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "simpr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "gsumval1.mm"
include "wi.mm"
include "simpl.mm"
include "ralimi.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "csn.mm"
include "fvex.mm"
include "snid.mm"
include "c0.mm"
include "wn.mm"
include "wne.mm"
include "cdm.mm"
include "fdm.mm"
include "cuz.mm"
include "eluzfz1.mm"
include "ne0i.mm"
include "3syl.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "wo.mm"
include "mgmidsssn0.mm"
include "sssn.mm"
include "orcanai.mm"
include "syldan.mm"
include "syl5eleqr.mm"
include "sseldi.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "sylbi.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "elsni.mm"
include "seqid3.mm"
include "eqtr4d.mm"
include "gsumval2a.mm"
include "pm2.61dan.mm"

theorem gsumval2
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cO: class O
  assume gsumval2.b: |- B = ( Base ` G )
  assume gsumval2.p: |- .+ = ( +g ` G )
  assume gsumval2.g: |- ( ph -> G e. V )
  assume gsumval2.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume gsumval2.f: |- ( ph -> F : ( M ... N ) --> B )


  assert |- ( ph -> ( G gsum F ) = ( seq M ( .+ , F ) ` N ) )

  proof
    wph
    cF
    crn
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    @1
    c.pl
    co
    @2
    wceq
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    crab
    #
    wss
    #
    cG
    cF
    cgsu
    co
    #
    cN
    c.pl
    cF
    cM
    cseq
    cfv
    #
    wceq
    wph
    @9
    wa
    #
    @10
    cG
    c0g
    cfv
    #
    @11
    @12
    vx
    vy
    cM
    cN
    cfz
    co
    #
    cB
    c.pl
    cF
    cG
    @8
    cV
    cvv
    @13
    gsumval2.b
    @13
    eqid
    #
    gsumval2.p
    @8
    eqid
    #
    wph
    cG
    cV
    wcel
    #
    @9
    gsumval2.g
    adantr
    @12
    cM
    cN
    cfz
    ovexd
    @12
    cF
    @14
    wfn
    #
    @9
    @14
    @8
    cF
    wf
    wph
    @18
    @9
    wph
    @14
    cB
    cF
    wf
    #
    @18
    gsumval2.f
    @14
    cB
    cF
    ffn
    syl
    adantr
    wph
    @9
    simpr
    #
    @14
    @8
    cF
    df-f
    sylanbrc
    #
    gsumval1
    @12
    vz
    c.pl
    cF
    cM
    cN
    @13
    @12
    @13
    @4
    vy
    cB
    wral
    #
    vx
    cB
    crab
    #
    wcel
    #
    @13
    @13
    c.pl
    co
    #
    @13
    wceq
    #
    @12
    @8
    @23
    @13
    @7
    @22
    vx
    cB
    @7
    @22
    wi
    @1
    cB
    wcel
    @6
    @4
    vy
    cB
    @4
    @5
    simpl
    ralimi
    a1i
    ss2rabi
    @12
    @13
    @13
    csn
    #
    @8
    @13
    cG
    c0g
    fvex
    snid
    wph
    @9
    @8
    c0
    wceq
    #
    wn
    @8
    @27
    wceq
    #
    @12
    @8
    c0
    @12
    @9
    @0
    c0
    wne
    #
    @8
    c0
    wne
    @20
    wph
    @30
    @9
    wph
    cF
    cdm
    #
    c0
    wne
    @30
    wph
    @31
    @14
    c0
    wph
    @19
    @31
    @14
    wceq
    gsumval2.f
    @14
    cB
    cF
    fdm
    syl
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    @14
    wcel
    @14
    c0
    wne
    gsumval2.n
    cM
    cN
    eluzfz1
    @14
    cM
    ne0i
    3syl
    eqnetrd
    @31
    c0
    @0
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    adantr
    @0
    @8
    ssn0
    syl2anc
    neneqd
    wph
    @28
    @29
    wph
    @8
    @27
    wss
    #
    @28
    @29
    wo
    wph
    @17
    @33
    gsumval2.g
    vx
    vy
    cB
    c.pl
    cG
    @8
    cV
    @13
    gsumval2.b
    @15
    gsumval2.p
    @16
    mgmidsssn0
    syl
    #
    @8
    @13
    sssn
    sylib
    orcanai
    syldan
    syl5eleqr
    sseldi
    @24
    @13
    cB
    wcel
    @13
    @2
    c.pl
    co
    #
    @2
    wceq
    #
    vy
    cB
    wral
    #
    wa
    @26
    @22
    @37
    vx
    @13
    cB
    @1
    @13
    wceq
    #
    @4
    @36
    vy
    cB
    @38
    @3
    @35
    @2
    @1
    @13
    @2
    c.pl
    oveq1
    eqeq1d
    ralbidv
    elrab
    @36
    @26
    vy
    @13
    cB
    @2
    @13
    wceq
    #
    @35
    @25
    @2
    @13
    @2
    @13
    @13
    c.pl
    oveq2
    @39
    id
    eqeq12d
    rspcva
    sylbi
    syl
    wph
    @32
    @9
    gsumval2.n
    adantr
    @12
    vz
    cv
    #
    @14
    wcel
    #
    wa
    #
    @40
    cF
    cfv
    #
    @27
    wcel
    @43
    @13
    wceq
    @42
    @8
    @27
    @43
    wph
    @33
    @9
    @41
    @34
    ad2antrr
    @12
    @14
    @8
    @40
    cF
    @21
    ffvelrnda
    sseldd
    @43
    @13
    elsni
    syl
    seqid3
    eqtr4d
    wph
    @9
    wn
    #
    wa
    vx
    vy
    cB
    c.pl
    cF
    cG
    cM
    cN
    @8
    cV
    gsumval2.b
    gsumval2.p
    wph
    @17
    @44
    gsumval2.g
    adantr
    wph
    @32
    @44
    gsumval2.n
    adantr
    wph
    @19
    @44
    gsumval2.f
    adantr
    @16
    wph
    @44
    simpr
    gsumval2a
    pm2.61dan
end
