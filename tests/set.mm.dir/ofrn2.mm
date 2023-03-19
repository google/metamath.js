include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "crn.mm"
include "cof.mm"
include "cxp.mm"
include "cima.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "simprl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "simprr.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "rexlimdvaa.mm"
include "ss2abdv.mm"
include "cmpt.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "rneqd.mm"
include "eqid.mm"
include "rnmpt.mm"
include "syl6eq.mm"
include "wss.mm"
include "wb.mm"
include "frn.mm"
include "xpss12.mm"
include "ovelimab.mm"
include "abbi2dv.mm"
include "3sstr4d.mm"

theorem ofrn2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vz: setvar z
  assume ofrn.1: |- ( ph -> F : A --> B )
  assume ofrn.2: |- ( ph -> G : A --> B )
  assume ofrn.3: |- ( ph -> .+ : ( B X. B ) --> C )
  assume ofrn.4: |- ( ph -> A e. V )


  assert |- ( ph -> ran ( F oF .+ G ) C_ ( .+ " ( ran F X. ran G ) ) )

  proof
    wph
    vz
    cv
    #
    va
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    va
    cA
    wrex
    #
    vz
    cab
    #
    @0
    vx
    cv
    vy
    cv
    c.pl
    co
    wceq
    vy
    cG
    crn
    #
    wrex
    vx
    cF
    crn
    #
    wrex
    #
    vz
    cab
    cF
    cG
    c.pl
    cof
    co
    #
    crn
    #
    c.pl
    @9
    @8
    cxp
    #
    cima
    #
    wph
    @6
    @10
    vz
    wph
    @5
    @10
    va
    cA
    wph
    @1
    cA
    wcel
    #
    @5
    wa
    #
    wa
    #
    @2
    @9
    wcel
    #
    @3
    @8
    wcel
    #
    @5
    @10
    @17
    cF
    cA
    wfn
    #
    @15
    @18
    wph
    @20
    @16
    wph
    cA
    cB
    cF
    wf
    #
    @20
    ofrn.1
    cA
    cB
    cF
    ffn
    syl
    #
    adantr
    wph
    @15
    @5
    simprl
    #
    cA
    @1
    cF
    fnfvelrn
    syl2anc
    @17
    cG
    cA
    wfn
    #
    @15
    @19
    wph
    @24
    @16
    wph
    cA
    cB
    cG
    wf
    #
    @24
    ofrn.2
    cA
    cB
    cG
    ffn
    syl
    #
    adantr
    @23
    cA
    @1
    cG
    fnfvelrn
    syl2anc
    wph
    @15
    @5
    simprr
    vx
    vy
    @9
    @8
    @2
    @3
    @0
    c.pl
    rspceov
    syl3anc
    rexlimdvaa
    ss2abdv
    wph
    @12
    va
    cA
    @4
    cmpt
    #
    crn
    @7
    wph
    @11
    @27
    wph
    va
    cA
    cA
    @2
    @3
    c.pl
    cA
    cF
    cG
    cV
    cV
    @22
    @26
    ofrn.4
    ofrn.4
    cA
    inidm
    wph
    @15
    wa
    #
    @2
    eqidd
    @28
    @3
    eqidd
    offval
    rneqd
    va
    vz
    cA
    @4
    @27
    @27
    eqid
    rnmpt
    syl6eq
    wph
    @10
    vz
    @14
    wph
    c.pl
    cB
    cB
    cxp
    #
    wfn
    #
    @13
    @29
    wss
    #
    @0
    @14
    wcel
    @10
    wb
    wph
    @29
    cC
    c.pl
    wf
    @30
    ofrn.3
    @29
    cC
    c.pl
    ffn
    syl
    wph
    @9
    cB
    wss
    #
    @8
    cB
    wss
    #
    @31
    wph
    @21
    @32
    ofrn.1
    cA
    cB
    cF
    frn
    syl
    wph
    @25
    @33
    ofrn.2
    cA
    cB
    cG
    frn
    syl
    @9
    cB
    @8
    cB
    xpss12
    syl2anc
    vx
    vy
    @29
    @9
    @8
    @0
    c.pl
    ovelimab
    syl2anc
    abbi2dv
    3sstr4d
end
