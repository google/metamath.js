include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cc0.mm"
include "climc.mm"
include "0cnd.mm"
include "2thd.mm"
include "csb.mm"
include "adantr.mm"
include "subcld.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "subid1d.mm"
include "wceq.mm"
include "simpr.mm"
include "cvv.mm"
include "vex.mm"
include "csbov1g.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wsb.mm"
include "sban.mm"
include "nfv.mm"
include "sbf.mm"
include "clelsb3.mm"
include "anbi12i.mm"
include "bitri.mm"
include "nfth.mm"
include "sbim.mm"
include "sylbb1.mm"
include "syl5bir.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "wb.mm"
include "sbcel1g.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "syl6reqr.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "ellimc3.mm"
include "3bitr4d.mm"

theorem ellimcabssub0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume ellimcabssub0.f: |- F = ( x e. A |-> B )
  assume ellimcabssub0.g: |- G = ( x e. A |-> ( B - C ) )
  assume ellimcabssub0.a: |- ( ph -> A C_ CC )
  assume ellimcabssub0.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume ellimcabssub0.p: |- ( ph -> D e. CC )
  assume ellimcabssub0.c: |- ( ph -> C e. CC )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( C e. ( F limCC D ) <-> 0 e. ( G limCC D ) ) )

  proof
    wph
    cC
    cc
    wcel
    #
    vz
    cv
    #
    cD
    wne
    @1
    cD
    cmin
    co
    cabs
    cfv
    vw
    cv
    clt
    wbr
    wa
    #
    @1
    cF
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vw
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    cc0
    cc
    wcel
    #
    @2
    @1
    cG
    cfv
    #
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vw
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    cC
    cF
    cD
    climc
    co
    wcel
    cc0
    cG
    cD
    climc
    co
    wcel
    wph
    @0
    @12
    @11
    @20
    wph
    @0
    @12
    ellimcabssub0.c
    wph
    0cnd
    2thd
    wph
    @10
    @19
    vy
    crp
    wph
    @9
    @18
    vw
    crp
    wph
    @8
    @17
    vz
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @7
    @16
    @2
    @22
    @5
    @15
    @6
    clt
    @22
    @4
    @14
    cabs
    @22
    @14
    @13
    vx
    @1
    cB
    cC
    cmin
    co
    #
    csb
    #
    @4
    @22
    @13
    wph
    cA
    cc
    @1
    cG
    wph
    vx
    cA
    @23
    cc
    cG
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    cB
    cC
    ellimcabssub0.b
    wph
    @0
    @25
    ellimcabssub0.c
    adantr
    subcld
    ellimcabssub0.g
    fmptd
    #
    ffvelrnda
    subid1d
    @22
    @21
    @24
    cc
    wcel
    @13
    @24
    wceq
    wph
    @21
    simpr
    #
    @22
    @24
    vx
    @1
    cB
    csb
    #
    cC
    cmin
    co
    #
    cc
    @24
    @30
    wceq
    #
    @22
    @1
    cvv
    wcel
    #
    @31
    vz
    vex
    #
    vx
    @1
    cB
    cC
    cmin
    cvv
    csbov1g
    ax-mp
    #
    a1i
    @22
    @29
    cC
    @22
    cB
    cc
    wcel
    #
    vx
    vz
    wsb
    #
    @29
    cc
    wcel
    #
    @26
    @35
    wi
    #
    @22
    @36
    wi
    ellimcabssub0.b
    @22
    @26
    vx
    vz
    wsb
    #
    @38
    @36
    @39
    wph
    vx
    vz
    wsb
    #
    @25
    vx
    vz
    wsb
    #
    wa
    @22
    wph
    @25
    vx
    vz
    sban
    @40
    wph
    @41
    @21
    wph
    vx
    vz
    wph
    vx
    nfv
    sbf
    vz
    vx
    cA
    clelsb3
    anbi12i
    bitri
    @38
    vx
    vz
    wsb
    @38
    @39
    @36
    wi
    @38
    vx
    vz
    @38
    vx
    ellimcabssub0.b
    nfth
    sbf
    @26
    @35
    vx
    vz
    sbim
    sylbb1
    syl5bir
    ax-mp
    @36
    @35
    vx
    @1
    wsbc
    #
    @37
    @35
    vx
    vz
    sbsbc
    @32
    @42
    @37
    wb
    @33
    vx
    @1
    cB
    cc
    cvv
    sbcel1g
    ax-mp
    bitri
    sylib
    #
    wph
    @0
    @21
    ellimcabssub0.c
    adantr
    subcld
    eqeltrd
    vx
    @1
    @23
    cA
    cG
    cc
    ellimcabssub0.g
    fvmpts
    syl2anc
    @22
    @4
    @30
    @24
    @22
    @3
    @29
    cC
    cmin
    @22
    @21
    @37
    @3
    @29
    wceq
    @28
    @43
    vx
    @1
    cB
    cA
    cF
    cc
    ellimcabssub0.f
    fvmpts
    syl2anc
    oveq1d
    @34
    syl6reqr
    3eqtrrd
    fveq2d
    breq1d
    imbi2d
    ralbidva
    rexbidv
    ralbidv
    anbi12d
    wph
    vy
    vw
    vz
    cA
    cD
    cC
    cF
    wph
    vx
    cA
    cB
    cc
    cF
    ellimcabssub0.b
    ellimcabssub0.f
    fmptd
    ellimcabssub0.a
    ellimcabssub0.p
    ellimc3
    wph
    vy
    vw
    vz
    cA
    cD
    cc0
    cG
    @27
    ellimcabssub0.a
    ellimcabssub0.p
    ellimc3
    3bitr4d
end
