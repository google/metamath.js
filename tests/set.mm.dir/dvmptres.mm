include "ctop.mm"
include "wcel.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "crest.mm"
include "co.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "cnfldtop.mm"
include "resttop.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "isopn3i.mm"
include "syl2anc.mm"
include "dvmptres2.mm"

theorem dvmptres
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let cW: class W
  let cZ: class Z
  assume dvmptadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptadd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptadd.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptadd.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptres.y: |- ( ph -> Y C_ X )
  assume dvmptres.j: |- J = ( K |`t S )
  assume dvmptres.k: |- K = ( TopOpen ` CCfld )
  assume dvmptres.t: |- ( ph -> Y e. J )

  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint Y x
  disjoint W x
  disjoint Z x
  assert |- ( ph -> ( S _D ( x e. Y |-> A ) ) = ( x e. Y |-> B ) )

  proof
    wph
    vx
    cA
    cB
    cS
    cJ
    cK
    cV
    cX
    cY
    cY
    dvmptadd.s
    dvmptadd.a
    dvmptadd.b
    dvmptadd.da
    dvmptres.y
    dvmptres.j
    dvmptres.k
    wph
    cJ
    ctop
    wcel
    cY
    cJ
    wcel
    cY
    cJ
    cnt
    cfv
    cfv
    cY
    wceq
    wph
    cJ
    cK
    cS
    crest
    co
    #
    ctop
    dvmptres.j
    wph
    cK
    ctop
    wcel
    cS
    cr
    cc
    cpr
    #
    wcel
    @0
    ctop
    wcel
    cK
    dvmptres.k
    cnfldtop
    dvmptadd.s
    cS
    cK
    @1
    resttop
    sylancr
    syl5eqel
    dvmptres.t
    cY
    cJ
    isopn3i
    syl2anc
    dvmptres2
end
