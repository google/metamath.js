include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cres.mm"
include "eqid.mm"
include "fmptd.mm"
include "gsumsplit.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem gsumsplit2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume gsumsplit2.b: |- B = ( Base ` G )
  assume gsumsplit2.z: |- .0. = ( 0g ` G )
  assume gsumsplit2.p: |- .+ = ( +g ` G )
  assume gsumsplit2.g: |- ( ph -> G e. CMnd )
  assume gsumsplit2.a: |- ( ph -> A e. V )
  assume gsumsplit2.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumsplit2.w: |- ( ph -> ( k e. A |-> X ) finSupp .0. )
  assume gsumsplit2.i: |- ( ph -> ( C i^i D ) = (/) )
  assume gsumsplit2.u: |- ( ph -> A = ( C u. D ) )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. A |-> X ) ) = ( ( G gsum ( k e. C |-> X ) ) .+ ( G gsum ( k e. D |-> X ) ) ) )

  proof
    wph
    cG
    vk
    cA
    cX
    cmpt
    #
    cgsu
    co
    cG
    @0
    cC
    cres
    #
    cgsu
    co
    #
    cG
    @0
    cD
    cres
    #
    cgsu
    co
    #
    c.pl
    co
    cG
    vk
    cC
    cX
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    cD
    cX
    cmpt
    #
    cgsu
    co
    #
    c.pl
    co
    wph
    cA
    cB
    cC
    cD
    c.pl
    @0
    cG
    cV
    c.0
    gsumsplit2.b
    gsumsplit2.z
    gsumsplit2.p
    gsumsplit2.g
    gsumsplit2.a
    wph
    vk
    cA
    cX
    cB
    @0
    gsumsplit2.f
    @0
    eqid
    fmptd
    gsumsplit2.w
    gsumsplit2.i
    gsumsplit2.u
    gsumsplit
    wph
    @2
    @6
    @4
    @8
    c.pl
    wph
    @1
    @5
    cG
    cgsu
    wph
    vk
    cA
    cC
    cX
    wph
    cC
    cD
    cun
    #
    cC
    cA
    cC
    cD
    ssun1
    gsumsplit2.u
    syl5sseqr
    resmptd
    oveq2d
    wph
    @3
    @7
    cG
    cgsu
    wph
    vk
    cA
    cD
    cX
    wph
    @9
    cD
    cA
    cD
    cC
    ssun2
    gsumsplit2.u
    syl5sseqr
    resmptd
    oveq2d
    oveq12d
    eqtrd
end
