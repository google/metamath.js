include "cdif.mm"
include "cun.mm"
include "ccarsg.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "elcarsgss.mm"
include "dfss4.mm"
include "sylib.mm"
include "uneq12d.mm"
include "cin.mm"
include "difindi.mm"
include "difelcarsg.mm"
include "inelcarsg.mm"
include "syl5eqelr.mm"
include "eqeltrrd.mm"

theorem unelcarsg
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
  assert |- ( ph -> ( A u. B ) e. ( toCaraSiga ` M ) )

  proof
    wph
    cO
    cO
    cA
    cdif
    #
    cdif
    #
    cO
    cO
    cB
    cdif
    #
    cdif
    #
    cun
    #
    cA
    cB
    cun
    cM
    ccarsg
    cfv
    #
    wph
    @1
    cA
    @3
    cB
    wph
    cA
    cO
    wss
    @1
    cA
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
    cO
    dfss4
    sylib
    wph
    cB
    cO
    wss
    @3
    cB
    wceq
    wph
    cB
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    inelcarsg.2
    elcarsgss
    cB
    cO
    dfss4
    sylib
    uneq12d
    wph
    @4
    cO
    @0
    @2
    cin
    #
    cdif
    @5
    cO
    @0
    @2
    difindi
    wph
    @6
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    wph
    @0
    @2
    cM
    cO
    cV
    va
    vb
    carsgval.1
    carsgval.2
    wph
    cA
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    difelcarsg.1
    difelcarsg
    inelcarsg.1
    wph
    cB
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    inelcarsg.2
    difelcarsg
    inelcarsg
    difelcarsg
    syl5eqelr
    eqeltrrd
end
