include "wcel.mm"
include "ralrimiva.mm"
include "evl1gsumd.mm"

theorem evl1gsumaddval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cK: class K
  let cN: class N
  let cW: class W
  let cY: class Y
  assume evl1gsumadd.q: |- Q = ( eval1 ` R )
  assume evl1gsumadd.k: |- K = ( Base ` R )
  assume evl1gsumadd.w: |- W = ( Poly1 ` R )
  assume evl1gsumadd.p: |- P = ( R ^s K )
  assume evl1gsumadd.b: |- B = ( Base ` W )
  assume evl1gsumadd.r: |- ( ph -> R e. CRing )
  assume evl1gsumadd.y: |- ( ( ph /\ x e. N ) -> Y e. B )
  assume evl1gsumadd.n: |- ( ph -> N C_ NN0 )
  assume evl1gsumaddval.f: |- ( ph -> N e. Fin )
  assume evl1gsumaddval.c: |- ( ph -> C e. K )

  disjoint C x
  disjoint B x
  disjoint K x
  disjoint N x
  disjoint Q x
  disjoint R x
  disjoint ph x
  assert |- ( ph -> ( ( Q ` ( W gsum ( x e. N |-> Y ) ) ) ` C ) = ( R gsum ( x e. N |-> ( ( Q ` Y ) ` C ) ) ) )

  proof
    wph
    vx
    cK
    cW
    cR
    cB
    cY
    cN
    cQ
    cC
    evl1gsumadd.q
    evl1gsumadd.w
    evl1gsumadd.k
    evl1gsumadd.b
    evl1gsumadd.r
    evl1gsumaddval.c
    wph
    cY
    cB
    wcel
    vx
    cN
    evl1gsumadd.y
    ralrimiva
    evl1gsumaddval.f
    evl1gsumd
end
