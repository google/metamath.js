include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cof.mm"
include "offval2.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "gsumsub.mm"
include "eqtrd.mm"

theorem gsummptfssub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cV: class V
  let c.0: class .0.
  assume gsummptfssub.b: |- B = ( Base ` G )
  assume gsummptfssub.z: |- .0. = ( 0g ` G )
  assume gsummptfssub.s: |- .- = ( -g ` G )
  assume gsummptfssub.g: |- ( ph -> G e. Abel )
  assume gsummptfssub.a: |- ( ph -> A e. V )
  assume gsummptfssub.c: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptfssub.d: |- ( ( ph /\ x e. A ) -> D e. B )
  assume gsummptfssub.f: |- ( ph -> F = ( x e. A |-> C ) )
  assume gsummptfssub.h: |- ( ph -> H = ( x e. A |-> D ) )
  assume gsummptfssub.w: |- ( ph -> F finSupp .0. )
  assume gsummptfssub.v: |- ( ph -> H finSupp .0. )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint .- x
  assert |- ( ph -> ( G gsum ( x e. A |-> ( C .- D ) ) ) = ( ( G gsum F ) .- ( G gsum H ) ) )

  proof
    wph
    cG
    vx
    cA
    cC
    cD
    c.mi
    co
    cmpt
    #
    cgsu
    co
    cG
    cF
    cH
    c.mi
    cof
    co
    #
    cgsu
    co
    cG
    cF
    cgsu
    co
    cG
    cH
    cgsu
    co
    c.mi
    co
    wph
    @0
    @1
    cG
    cgsu
    wph
    @1
    @0
    wph
    vx
    cA
    cC
    cD
    c.mi
    cF
    cH
    cV
    cB
    cB
    gsummptfssub.a
    gsummptfssub.c
    gsummptfssub.d
    gsummptfssub.f
    gsummptfssub.h
    offval2
    eqcomd
    oveq2d
    wph
    cA
    cB
    cF
    cG
    cH
    c.mi
    cV
    c.0
    gsummptfssub.b
    gsummptfssub.z
    gsummptfssub.s
    gsummptfssub.g
    gsummptfssub.a
    wph
    cA
    cB
    cF
    wf
    cA
    cB
    vx
    cA
    cC
    cmpt
    #
    wf
    wph
    vx
    cA
    cC
    cB
    @2
    gsummptfssub.c
    @2
    eqid
    fmptd
    wph
    cA
    cB
    cF
    @2
    gsummptfssub.f
    feq1d
    mpbird
    wph
    cA
    cB
    cH
    wf
    cA
    cB
    vx
    cA
    cD
    cmpt
    #
    wf
    wph
    vx
    cA
    cD
    cB
    @3
    gsummptfssub.d
    @3
    eqid
    fmptd
    wph
    cA
    cB
    cH
    @3
    gsummptfssub.h
    feq1d
    mpbird
    gsummptfssub.w
    gsummptfssub.v
    gsumsub
    eqtrd
end
