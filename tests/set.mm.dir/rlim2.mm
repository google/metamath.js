include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "wf.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "eqidd.mm"
include "rlim.mm"
include "biantrurd.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfov.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "weq.mm"
include "breq2.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "wb.mm"
include "fvmpt2.mm"
include "imbi2d.mm"
include "ralimiaa.mm"
include "ralbi.mm"
include "3syl.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "3bitr2d.mm"

theorem rlim2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let cD: class D
  assume rlim2.1: |- ( ph -> A. z e. A B e. CC )
  assume rlim2.2: |- ( ph -> A C_ RR )
  assume rlim2.3: |- ( ph -> C e. CC )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint ph w
  disjoint D w
  disjoint D y
  disjoint D z
  assert |- ( ph -> ( ( z e. A |-> B ) ~~>r C <-> A. x e. RR+ E. y e. RR A. z e. A ( y <_ z -> ( abs ` ( B - C ) ) < x ) ) )

  proof
    wph
    vz
    cA
    cB
    cmpt
    #
    cC
    crli
    wbr
    cC
    cc
    wcel
    #
    vy
    cv
    #
    vw
    cv
    #
    cle
    wbr
    #
    @3
    @0
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @13
    @2
    vz
    cv
    #
    cle
    wbr
    #
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    wph
    vx
    vy
    vw
    cA
    @5
    cC
    @0
    wph
    cB
    cc
    wcel
    #
    vz
    cA
    wral
    #
    cA
    cc
    @0
    wf
    rlim2.1
    vz
    cA
    cc
    cB
    @0
    @0
    eqid
    #
    fmpt
    sylib
    rlim2.2
    wph
    @3
    cA
    wcel
    wa
    @5
    eqidd
    rlim
    wph
    @1
    @13
    rlim2.3
    biantrurd
    wph
    @12
    @21
    vx
    crp
    wph
    @11
    @20
    vy
    cr
    @11
    @15
    @14
    @0
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    wph
    @20
    @10
    @29
    vw
    vz
    cA
    @4
    @9
    vz
    @4
    vz
    nfv
    vz
    @7
    @8
    clt
    vz
    @6
    cabs
    vz
    cabs
    nfcv
    vz
    @5
    cC
    cmin
    vz
    cA
    cB
    @3
    nffvmpt1
    vz
    cmin
    nfcv
    vz
    cC
    nfcv
    nfov
    nffv
    vz
    clt
    nfcv
    vz
    @8
    nfcv
    nfbr
    nfim
    @29
    vw
    nfv
    vw
    vz
    weq
    #
    @4
    @15
    @9
    @28
    @3
    @14
    @2
    cle
    breq2
    @31
    @7
    @27
    @8
    clt
    @31
    @6
    @26
    cabs
    @31
    @5
    @25
    cC
    cmin
    @3
    @14
    @0
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    cbvral
    wph
    @23
    @29
    @19
    wb
    #
    vz
    cA
    wral
    @30
    @20
    wb
    rlim2.1
    @22
    @32
    vz
    cA
    @14
    cA
    wcel
    @22
    wa
    #
    @28
    @18
    @15
    @33
    @27
    @17
    @8
    clt
    @33
    @26
    @16
    cabs
    @33
    @25
    cB
    cC
    cmin
    vz
    cA
    cB
    cc
    @0
    @24
    fvmpt2
    oveq1d
    fveq2d
    breq1d
    imbi2d
    ralimiaa
    @29
    @19
    vz
    cA
    ralbi
    3syl
    syl5bb
    rexbidv
    ralbidv
    3bitr2d
end
