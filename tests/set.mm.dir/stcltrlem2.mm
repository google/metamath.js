include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cort.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wi.mm"
include "wss.mm"
include "stcltrlem1.mm"
include "choccli.mm"
include "chincli.mm"
include "chjcli.mm"
include "stcltr1i.mm"
include "mpd.mm"

theorem stcltrlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  assume stcltr1.1: |- ( ph <-> ( S e. States /\ A. x e. CH A. y e. CH ( ( ( S ` x ) = 1 -> ( S ` y ) = 1 ) -> x C_ y ) ) )
  assume stcltr1.2: |- A e. CH
  assume stcltrlem1.3: |- B e. CH

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  assert |- ( ph -> B C_ ( ( _|_ ` A ) vH ( A i^i B ) ) )

  proof
    wph
    cB
    cS
    cfv
    c1
    wceq
    cA
    cort
    cfv
    #
    cA
    cB
    cin
    #
    chj
    co
    #
    cS
    cfv
    c1
    wceq
    wi
    cB
    @2
    wss
    wph
    vx
    vy
    cA
    cB
    cS
    stcltr1.1
    stcltr1.2
    stcltrlem1.3
    stcltrlem1
    wph
    vx
    vy
    cB
    @2
    cS
    stcltr1.1
    stcltrlem1.3
    @0
    @1
    cA
    stcltr1.2
    choccli
    cA
    cB
    stcltr1.2
    stcltrlem1.3
    chincli
    chjcli
    stcltr1i
    mpd
end
