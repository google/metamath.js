include "chtpy.mm"
include "co.mm"
include "wcel.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "cv.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ishtpy.mm"
include "mpbir2and.mm"

theorem ishtpyd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ishtpy.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume ishtpy.3: |- ( ph -> F e. ( J Cn K ) )
  assume ishtpy.4: |- ( ph -> G e. ( J Cn K ) )
  assume ishtpyd.1: |- ( ph -> H e. ( ( J tX II ) Cn K ) )
  assume ishtpyd.2: |- ( ( ph /\ s e. X ) -> ( s H 0 ) = ( F ` s ) )
  assume ishtpyd.3: |- ( ( ph /\ s e. X ) -> ( s H 1 ) = ( G ` s ) )

  disjoint F s
  disjoint G s
  disjoint H s
  disjoint J s
  disjoint ph s
  disjoint X s
  disjoint A s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint F g
  disjoint h s
  disjoint h t
  disjoint F h
  disjoint s t
  disjoint F t
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G t
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint H x
  disjoint H y
  disjoint M t
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint g j
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint h j
  disjoint h k
  disjoint h z
  disjoint J h
  disjoint j k
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint J k
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint x z
  disjoint J x
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint K j
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X j
  disjoint X k
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> H e. ( F ( J Htpy K ) G ) )

  proof
    wph
    cH
    cF
    cG
    cJ
    cK
    chtpy
    co
    co
    wcel
    cH
    cJ
    cii
    ctx
    co
    cK
    ccn
    co
    wcel
    vs
    cv
    #
    cc0
    cH
    co
    @0
    cF
    cfv
    wceq
    #
    @0
    c1
    cH
    co
    @0
    cG
    cfv
    wceq
    #
    wa
    #
    vs
    cX
    wral
    ishtpyd.1
    wph
    @3
    vs
    cX
    wph
    @0
    cX
    wcel
    wa
    @1
    @2
    ishtpyd.2
    ishtpyd.3
    jca
    ralrimiva
    wph
    cF
    cG
    cH
    cJ
    cK
    cX
    vs
    ishtpy.1
    ishtpy.3
    ishtpy.4
    ishtpy
    mpbir2and
end
