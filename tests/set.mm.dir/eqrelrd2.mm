include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "alrimi.mm"
include "adantl.mm"
include "wss.mm"
include "wi.mm"
include "ssrelf.mm"
include "bi2anan9.mm"
include "eqss.mm"
include "2albiim.mm"
include "3bitr4g.mm"
include "adantr.mm"
include "mpbird.mm"

theorem eqrelrd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume eqrelrd2.1: |- F/ x ph
  assume eqrelrd2.2: |- F/ y ph
  assume eqrelrd2.3: |- F/_ x A
  assume eqrelrd2.4: |- F/_ y A
  assume eqrelrd2.5: |- F/_ x B
  assume eqrelrd2.6: |- F/_ y B
  assume eqrelrd2.7: |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B )

  proof
    cA
    wrel
    #
    cB
    wrel
    #
    wa
    #
    wph
    wa
    cA
    cB
    wceq
    #
    vx
    cv
    vy
    cv
    cop
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wb
    #
    vy
    wal
    #
    vx
    wal
    #
    wph
    @9
    @2
    wph
    @8
    vx
    eqrelrd2.1
    wph
    @7
    vy
    eqrelrd2.2
    eqrelrd2.7
    alrimi
    alrimi
    adantl
    @2
    @3
    @9
    wb
    wph
    @2
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    @5
    @6
    wi
    vy
    wal
    vx
    wal
    #
    @6
    @5
    wi
    vy
    wal
    vx
    wal
    #
    wa
    @3
    @9
    @0
    @10
    @12
    @1
    @11
    @13
    wph
    vx
    vy
    cA
    cB
    eqrelrd2.1
    eqrelrd2.2
    eqrelrd2.3
    eqrelrd2.4
    eqrelrd2.5
    eqrelrd2.6
    ssrelf
    wph
    vx
    vy
    cB
    cA
    eqrelrd2.1
    eqrelrd2.2
    eqrelrd2.5
    eqrelrd2.6
    eqrelrd2.3
    eqrelrd2.4
    ssrelf
    bi2anan9
    cA
    cB
    eqss
    @5
    @6
    vx
    vy
    2albiim
    3bitr4g
    adantr
    mpbird
end
