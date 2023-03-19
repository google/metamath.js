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
include "gsumadd.mm"
include "eqtrd.mm"

theorem gsummptfsadd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let c.0: class .0.
  assume gsummptfsadd.b: |- B = ( Base ` G )
  assume gsummptfsadd.z: |- .0. = ( 0g ` G )
  assume gsummptfsadd.p: |- .+ = ( +g ` G )
  assume gsummptfsadd.g: |- ( ph -> G e. CMnd )
  assume gsummptfsadd.a: |- ( ph -> A e. V )
  assume gsummptfsadd.c: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptfsadd.d: |- ( ( ph /\ x e. A ) -> D e. B )
  assume gsummptfsadd.f: |- ( ph -> F = ( x e. A |-> C ) )
  assume gsummptfsadd.h: |- ( ph -> H = ( x e. A |-> D ) )
  assume gsummptfsadd.w: |- ( ph -> F finSupp .0. )
  assume gsummptfsadd.v: |- ( ph -> H finSupp .0. )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint .+ x
  assert |- ( ph -> ( G gsum ( x e. A |-> ( C .+ D ) ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) )

  proof
    wph
    cG
    vx
    cA
    cC
    cD
    c.pl
    co
    cmpt
    #
    cgsu
    co
    cG
    cF
    cH
    c.pl
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
    c.pl
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
    c.pl
    cF
    cH
    cV
    cB
    cB
    gsummptfsadd.a
    gsummptfsadd.c
    gsummptfsadd.d
    gsummptfsadd.f
    gsummptfsadd.h
    offval2
    eqcomd
    oveq2d
    wph
    cA
    cB
    c.pl
    cF
    cG
    cH
    cV
    c.0
    gsummptfsadd.b
    gsummptfsadd.z
    gsummptfsadd.p
    gsummptfsadd.g
    gsummptfsadd.a
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
    gsummptfsadd.c
    @2
    eqid
    fmptd
    wph
    cA
    cB
    cF
    @2
    gsummptfsadd.f
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
    gsummptfsadd.d
    @3
    eqid
    fmptd
    wph
    cA
    cB
    cH
    @3
    gsummptfsadd.h
    feq1d
    mpbird
    gsummptfsadd.w
    gsummptfsadd.v
    gsumadd
    eqtrd
end
