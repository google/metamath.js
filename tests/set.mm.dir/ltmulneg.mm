include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "negelrpd.mm"
include "ltmul1d.mm"
include "renegcld.mm"
include "remulcld.mm"
include "ltnegd.mm"
include "recnd.mm"
include "mulneg2d.mm"
include "negnegd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "breq12d.mm"
include "3bitrd.mm"

theorem ltmulneg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmulneg.a: |- ( ph -> A e. RR )
  assume ltmulneg.b: |- ( ph -> B e. RR )
  assume ltmulneg.c: |- ( ph -> C e. RR )
  assume ltmulneg.n: |- ( ph -> C < 0 )


  assert |- ( ph -> ( A < B <-> ( B x. C ) < ( A x. C ) ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cA
    cC
    cneg
    #
    cmul
    co
    #
    cB
    @0
    cmul
    co
    #
    clt
    wbr
    @2
    cneg
    #
    @1
    cneg
    #
    clt
    wbr
    cB
    cC
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    clt
    wbr
    wph
    cA
    cB
    @0
    ltmulneg.a
    ltmulneg.b
    wph
    cC
    ltmulneg.c
    ltmulneg.n
    negelrpd
    ltmul1d
    wph
    @1
    @2
    wph
    cA
    @0
    ltmulneg.a
    wph
    cC
    ltmulneg.c
    renegcld
    #
    remulcld
    wph
    cB
    @0
    ltmulneg.b
    @7
    remulcld
    ltnegd
    wph
    @3
    @5
    @4
    @6
    clt
    wph
    cB
    @0
    cneg
    #
    cmul
    co
    @3
    @5
    wph
    cB
    @0
    wph
    cB
    ltmulneg.b
    recnd
    wph
    @0
    @7
    recnd
    #
    mulneg2d
    wph
    @8
    cC
    cB
    cmul
    wph
    cC
    wph
    cC
    ltmulneg.c
    recnd
    negnegd
    #
    oveq2d
    eqtr3d
    wph
    cA
    @8
    cmul
    co
    @4
    @6
    wph
    cA
    @0
    wph
    cA
    ltmulneg.a
    recnd
    @9
    mulneg2d
    wph
    @8
    cC
    cA
    cmul
    @10
    oveq2d
    eqtr3d
    breq12d
    3bitrd
end
