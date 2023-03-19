include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmpt.mm"
include "crli.mm"
include "cc.mm"
include "wf.mm"
include "cdm.mm"
include "rlimf.mm"
include "syl.mm"
include "wceq.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "fdm.mm"
include "feq2d.mm"
include "mpbid.mm"
include "sylibr.mm"
include "wss.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "rlimcl.mm"
include "rlim2.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "sylc.mm"

theorem rlimi
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let vx: setvar x
  let cD: class D
  assume rlimi.1: |- ( ph -> A. z e. A B e. V )
  assume rlimi.2: |- ( ph -> R e. RR+ )
  assume rlimi.3: |- ( ph -> ( z e. A |-> B ) ~~>r C )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint C y
  disjoint C z
  disjoint ph y
  disjoint R y
  disjoint R z
  disjoint V z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint R x
  disjoint D y
  disjoint D z
  assert |- ( ph -> E. y e. RR A. z e. A ( y <_ z -> ( abs ` ( B - C ) ) < R ) )

  proof
    wph
    cR
    crp
    wcel
    vy
    cv
    vz
    cv
    cle
    wbr
    #
    cB
    cC
    cmin
    co
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
    vz
    cA
    wral
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    @0
    @1
    cR
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    vy
    cr
    wrex
    #
    rlimi.2
    wph
    vz
    cA
    cB
    cmpt
    #
    cC
    crli
    wbr
    #
    @6
    rlimi.3
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    wph
    cA
    cc
    @10
    wf
    #
    cB
    cc
    wcel
    vz
    cA
    wral
    wph
    @10
    cdm
    #
    cc
    @10
    wf
    #
    @12
    wph
    @11
    @14
    rlimi.3
    cC
    @10
    rlimf
    syl
    wph
    @13
    cA
    cc
    @10
    wph
    cA
    cV
    @10
    wf
    #
    @13
    cA
    wceq
    wph
    cB
    cV
    wcel
    vz
    cA
    wral
    @15
    rlimi.1
    vz
    cA
    cV
    cB
    @10
    @10
    eqid
    #
    fmpt
    sylib
    cA
    cV
    @10
    fdm
    syl
    #
    feq2d
    mpbid
    vz
    cA
    cc
    cB
    @10
    @16
    fmpt
    sylibr
    wph
    cA
    @13
    cr
    @17
    wph
    @11
    @13
    cr
    wss
    rlimi.3
    cC
    @10
    rlimss
    syl
    eqsstr3d
    wph
    @11
    cC
    cc
    wcel
    rlimi.3
    cC
    @10
    rlimcl
    syl
    rlim2
    mpbid
    @5
    @9
    vx
    cR
    crp
    @2
    cR
    wceq
    #
    @4
    @8
    vy
    vz
    cr
    cA
    @18
    @3
    @7
    @0
    @2
    cR
    @1
    clt
    breq2
    imbi2d
    rexralbidv
    rspcv
    sylc
end
