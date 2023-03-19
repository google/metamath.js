include "cv.mm"
include "wceq.mm"
include "adantl.mm"
include "gsumunsnfd.mm"

theorem gsumunsnf
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
  assume gsumunsnf.0: |- F/_ k Y
  assume gsumunsnf.b: |- B = ( Base ` G )
  assume gsumunsnf.p: |- .+ = ( +g ` G )
  assume gsumunsnf.g: |- ( ph -> G e. CMnd )
  assume gsumunsnf.a: |- ( ph -> A e. Fin )
  assume gsumunsnf.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumunsnf.m: |- ( ph -> M e. V )
  assume gsumunsnf.d: |- ( ph -> -. M e. A )
  assume gsumunsnf.y: |- ( ph -> Y e. B )
  assume gsumunsnf.s: |- ( k = M -> X = Y )

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint M k
  disjoint V k
  disjoint k ph
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
    gsumunsnf.b
    gsumunsnf.p
    gsumunsnf.g
    gsumunsnf.a
    gsumunsnf.f
    gsumunsnf.m
    gsumunsnf.d
    gsumunsnf.y
    vk
    cv
    cM
    wceq
    cX
    cY
    wceq
    wph
    gsumunsnf.s
    adantl
    gsumunsnf.0
    gsumunsnfd
end
