include "nfcv.mm"
include "gsumunsnfd.mm"

theorem gsumunsnd
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
  assume gsumunsnd.b: |- B = ( Base ` G )
  assume gsumunsnd.p: |- .+ = ( +g ` G )
  assume gsumunsnd.g: |- ( ph -> G e. CMnd )
  assume gsumunsnd.a: |- ( ph -> A e. Fin )
  assume gsumunsnd.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumunsnd.m: |- ( ph -> M e. V )
  assume gsumunsnd.d: |- ( ph -> -. M e. A )
  assume gsumunsnd.y: |- ( ph -> Y e. B )
  assume gsumunsnd.s: |- ( ( ph /\ k = M ) -> X = Y )

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
    gsumunsnd.b
    gsumunsnd.p
    gsumunsnd.g
    gsumunsnd.a
    gsumunsnd.f
    gsumunsnd.m
    gsumunsnd.d
    gsumunsnd.y
    gsumunsnd.s
    vk
    cY
    nfcv
    gsumunsnfd
end
