include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "adantr.mm"
include "cr.mm"
include "wcel.mm"
include "recnd.mm"
include "mul02d.mm"
include "breqtrrd.mm"
include "0red.mm"
include "simpr.mm"
include "elrpd.mm"
include "ltmul1d.mm"
include "mpbird.mm"

theorem mul2lt0rgt0
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mul2lt0.1: |- ( ph -> A e. RR )
  assume mul2lt0.2: |- ( ph -> B e. RR )
  assume mul2lt0.3: |- ( ph -> ( A x. B ) < 0 )


  assert |- ( ( ph /\ 0 < B ) -> A < 0 )

  proof
    wph
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    cA
    cc0
    clt
    wbr
    cA
    cB
    cmul
    co
    #
    cc0
    cB
    cmul
    co
    #
    clt
    wbr
    @1
    @2
    cc0
    @3
    clt
    wph
    @2
    cc0
    clt
    wbr
    @0
    mul2lt0.3
    adantr
    @1
    cB
    @1
    cB
    wph
    cB
    cr
    wcel
    @0
    mul2lt0.2
    adantr
    #
    recnd
    mul02d
    breqtrrd
    @1
    cA
    cc0
    cB
    wph
    cA
    cr
    wcel
    @0
    mul2lt0.1
    adantr
    @1
    0red
    @1
    cB
    @4
    wph
    @0
    simpr
    elrpd
    ltmul1d
    mpbird
end
