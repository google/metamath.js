include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "remulcld.mm"
include "adantr.mm"
include "0red.mm"
include "crp.mm"
include "wb.mm"
include "negelrp.mm"
include "syl.mm"
include "biimpar.mm"
include "ltdiv1dd.mm"
include "cc.mm"
include "recnd.mm"
include "mulcld.mm"
include "simpr.mm"
include "lt0ne0d.mm"
include "divneg2d.mm"
include "divcan4d.mm"
include "negeqd.mm"
include "eqtr3d.mm"
include "negcld.mm"
include "negne0d.mm"
include "div0d.mm"
include "3brtr3d.mm"
include "lt0neg2d.mm"
include "mpbird.mm"

theorem mul2lt0rlt0
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mul2lt0.1: |- ( ph -> A e. RR )
  assume mul2lt0.2: |- ( ph -> B e. RR )
  assume mul2lt0.3: |- ( ph -> ( A x. B ) < 0 )


  assert |- ( ( ph /\ B < 0 ) -> 0 < A )

  proof
    wph
    cB
    cc0
    clt
    wbr
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    cA
    cneg
    #
    cc0
    clt
    wbr
    @1
    cA
    cB
    cmul
    co
    #
    cB
    cneg
    #
    cdiv
    co
    #
    cc0
    @4
    cdiv
    co
    @2
    cc0
    clt
    @1
    @3
    cc0
    @4
    wph
    @3
    cr
    wcel
    @0
    wph
    cA
    cB
    mul2lt0.1
    mul2lt0.2
    remulcld
    adantr
    @1
    0red
    wph
    @4
    crp
    wcel
    #
    @0
    wph
    cB
    cr
    wcel
    @6
    @0
    wb
    mul2lt0.2
    cB
    negelrp
    syl
    biimpar
    wph
    @3
    cc0
    clt
    wbr
    @0
    mul2lt0.3
    adantr
    ltdiv1dd
    @1
    @3
    cB
    cdiv
    co
    #
    cneg
    @5
    @2
    @1
    @3
    cB
    @1
    cA
    cB
    wph
    cA
    cc
    wcel
    @0
    wph
    cA
    mul2lt0.1
    recnd
    adantr
    #
    wph
    cB
    cc
    wcel
    @0
    wph
    cB
    mul2lt0.2
    recnd
    adantr
    #
    mulcld
    @9
    @1
    cB
    wph
    @0
    simpr
    lt0ne0d
    #
    divneg2d
    @1
    @7
    cA
    @1
    cA
    cB
    @8
    @9
    @10
    divcan4d
    negeqd
    eqtr3d
    @1
    @4
    @1
    cB
    @9
    negcld
    @1
    cB
    @9
    @10
    negne0d
    div0d
    3brtr3d
    @1
    cA
    wph
    cA
    cr
    wcel
    @0
    mul2lt0.1
    adantr
    lt0neg2d
    mpbird
end
