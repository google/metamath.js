include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "0cnd.mm"
include "rlim2lt.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "subid1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralimi.mm"
include "ralbi.mm"
include "3syl.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem rlim0lt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume rlim0.1: |- ( ph -> A. z e. A B e. CC )
  assume rlim0.2: |- ( ph -> A C_ RR )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( z e. A |-> B ) ~~>r 0 <-> A. x e. RR+ E. y e. RR A. z e. A ( y < z -> ( abs ` B ) < x ) ) )

  proof
    wph
    vz
    cA
    cB
    cmpt
    cc0
    crli
    wbr
    vy
    cv
    vz
    cv
    clt
    wbr
    #
    cB
    cc0
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
    @0
    cB
    cabs
    cfv
    #
    @3
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
    vz
    cA
    cB
    cc0
    rlim0.1
    rlim0.2
    wph
    0cnd
    rlim2lt
    wph
    @7
    @12
    vx
    crp
    wph
    @6
    @11
    vy
    cr
    wph
    cB
    cc
    wcel
    #
    vz
    cA
    wral
    @5
    @10
    wb
    #
    vz
    cA
    wral
    @6
    @11
    wb
    rlim0.1
    @13
    @14
    vz
    cA
    @13
    @4
    @9
    @0
    @13
    @2
    @8
    @3
    clt
    @13
    @1
    cB
    cabs
    cB
    subid1
    fveq2d
    breq1d
    imbi2d
    ralimi
    @5
    @10
    vz
    cA
    ralbi
    3syl
    rexbidv
    ralbidv
    bitrd
end
