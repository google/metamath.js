include "cv.mm"
include "wceq.mm"
include "adantl.mm"
include "gsumunsnd.mm"

theorem gsumunsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  assume gsumunsn.b: |- B = ( Base ` G )
  assume gsumunsn.p: |- .+ = ( +g ` G )
  assume gsumunsn.g: |- ( ph -> G e. CMnd )
  assume gsumunsn.a: |- ( ph -> A e. Fin )
  assume gsumunsn.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumunsn.m: |- ( ph -> M e. V )
  assume gsumunsn.d: |- ( ph -> -. M e. A )
  assume gsumunsn.y: |- ( ph -> Y e. B )
  assume gsumunsn.s: |- ( k = M -> X = Y )

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Y k
  assert |- ( ph -> ( G gsum ( k e. ( A u. { M } ) |-> X ) ) = ( ( G gsum ( k e. A |-> X ) ) .+ Y ) )

  proof
    wph
    cA
    cB
    c.pl
    vk
    cG
    cM
    cV
    cX
    cY
    gsumunsn.b
    gsumunsn.p
    gsumunsn.g
    gsumunsn.a
    gsumunsn.f
    gsumunsn.m
    gsumunsn.d
    gsumunsn.y
    vk
    cv
    cM
    wceq
    cX
    cY
    wceq
    wph
    gsumunsn.s
    adantl
    gsumunsnd
end
