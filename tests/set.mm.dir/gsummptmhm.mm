include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "eqidd.mm"
include "wfn.mm"
include "wceq.mm"
include "cmhm.mm"
include "wcel.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "mhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "dffn5.mm"
include "sylib.mm"
include "fveq2.mm"
include "fmptco.mm"
include "oveq2d.mm"
include "fmptd.mm"
include "gsummhm.mm"
include "eqtr3d.mm"

theorem gsummptmhm
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let vy: setvar y
  assume gsummptmhm.b: |- B = ( Base ` G )
  assume gsummptmhm.z: |- .0. = ( 0g ` G )
  assume gsummptmhm.g: |- ( ph -> G e. CMnd )
  assume gsummptmhm.h: |- ( ph -> H e. Mnd )
  assume gsummptmhm.a: |- ( ph -> A e. V )
  assume gsummptmhm.k: |- ( ph -> K e. ( G MndHom H ) )
  assume gsummptmhm.c: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptmhm.w: |- ( ph -> ( x e. A |-> C ) finSupp .0. )

  disjoint A x
  disjoint B x
  disjoint K x
  disjoint ph x
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint K y
  assert |- ( ph -> ( H gsum ( x e. A |-> ( K ` C ) ) ) = ( K ` ( G gsum ( x e. A |-> C ) ) ) )

  proof
    wph
    cH
    cK
    vx
    cA
    cC
    cmpt
    #
    ccom
    #
    cgsu
    co
    cH
    vx
    cA
    cC
    cK
    cfv
    #
    cmpt
    #
    cgsu
    co
    cG
    @0
    cgsu
    co
    cK
    cfv
    wph
    @1
    @3
    cH
    cgsu
    wph
    vx
    vy
    cA
    cB
    cC
    vy
    cv
    #
    cK
    cfv
    #
    @2
    @0
    cK
    gsummptmhm.c
    wph
    @0
    eqidd
    wph
    cK
    cB
    wfn
    #
    cK
    vy
    cB
    @5
    cmpt
    wceq
    wph
    cK
    cG
    cH
    cmhm
    co
    wcel
    cB
    cH
    cbs
    cfv
    #
    cK
    wf
    @6
    gsummptmhm.k
    cB
    @7
    cG
    cH
    cK
    gsummptmhm.b
    @7
    eqid
    mhmf
    cB
    @7
    cK
    ffn
    3syl
    vy
    cB
    cK
    dffn5
    sylib
    @4
    cC
    cK
    fveq2
    fmptco
    oveq2d
    wph
    cA
    cB
    @0
    cG
    cH
    cK
    cV
    c.0
    gsummptmhm.b
    gsummptmhm.z
    gsummptmhm.g
    gsummptmhm.h
    gsummptmhm.a
    gsummptmhm.k
    wph
    vx
    cA
    cC
    cB
    @0
    gsummptmhm.c
    @0
    eqid
    fmptd
    gsummptmhm.w
    gsummhm
    eqtr3d
end
