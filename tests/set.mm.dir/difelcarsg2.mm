include "cdif.mm"
include "cin.mm"
include "ccarsg.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "elcarsgss.mm"
include "difin2.mm"
include "syl.mm"
include "difelcarsg.mm"
include "inelcarsg.mm"
include "eqeltrd.mm"

theorem difelcarsg2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let ve: setvar e
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume difelcarsg.1: |- ( ph -> A e. ( toCaraSiga ` M ) )
  assume inelcarsg.1: |- ( ( ph /\ a e. ~P O /\ b e. ~P O ) -> ( M ` ( a u. b ) ) <_ ( ( M ` a ) +e ( M ` b ) ) )
  assume inelcarsg.2: |- ( ph -> B e. ( toCaraSiga ` M ) )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint M a
  disjoint M b
  disjoint O a
  disjoint O b
  disjoint a ph
  disjoint b ph
  disjoint M a
  disjoint O a
  disjoint a ph
  disjoint A a
  disjoint A f
  disjoint a f
  disjoint b f
  disjoint B e
  disjoint B f
  disjoint a e
  disjoint b e
  disjoint e f
  disjoint M f
  disjoint O f
  disjoint f ph
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O e
  disjoint O m
  disjoint e ph
  disjoint m ph
  disjoint A e
  assert |- ( ph -> ( A \ B ) e. ( toCaraSiga ` M ) )

  proof
    wph
    cA
    cB
    cdif
    #
    cO
    cB
    cdif
    #
    cA
    cin
    #
    cM
    ccarsg
    cfv
    wph
    cA
    cO
    wss
    @0
    @2
    wceq
    wph
    cA
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    difelcarsg.1
    elcarsgss
    cA
    cB
    cO
    difin2
    syl
    wph
    @1
    cA
    cM
    cO
    cV
    va
    vb
    carsgval.1
    carsgval.2
    wph
    cB
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    inelcarsg.2
    difelcarsg
    inelcarsg.1
    difelcarsg.1
    inelcarsg
    eqeltrd
end
