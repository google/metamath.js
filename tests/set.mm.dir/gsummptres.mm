include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cin.mm"
include "cdif.mm"
include "cplusg.mm"
include "cfv.mm"
include "cfn.mm"
include "eqid.mm"
include "cvv.mm"
include "wcel.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppmptdm.mm"
include "c0.mm"
include "wceq.mm"
include "inindif.mm"
include "cun.mm"
include "inundif.mm"
include "eqcomi.mm"
include "gsumsplit2.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "ccmn.mm"
include "cmnmnd.mm"
include "syl.mm"
include "diffi.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "infi.mm"
include "cv.mm"
include "inss1.mm"
include "sseli.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "mndrid.mm"

theorem gsummptres
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let c.0: class .0.
  assume gsummptres.0: |- B = ( Base ` G )
  assume gsummptres.1: |- .0. = ( 0g ` G )
  assume gsummptres.2: |- ( ph -> G e. CMnd )
  assume gsummptres.3: |- ( ph -> A e. Fin )
  assume gsummptres.4: |- ( ( ph /\ x e. A ) -> C e. B )
  assume gsummptres.5: |- ( ( ph /\ x e. ( A \ D ) ) -> C = .0. )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint G x
  disjoint ph x
  assert |- ( ph -> ( G gsum ( x e. A |-> C ) ) = ( G gsum ( x e. ( A i^i D ) |-> C ) ) )

  proof
    wph
    cG
    vx
    cA
    cC
    cmpt
    #
    cgsu
    co
    cG
    vx
    cA
    cD
    cin
    #
    cC
    cmpt
    cgsu
    co
    #
    cG
    vx
    cA
    cD
    cdif
    #
    cC
    cmpt
    #
    cgsu
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    wph
    cA
    cB
    @1
    @3
    @6
    vx
    cG
    cfn
    cC
    c.0
    gsummptres.0
    gsummptres.1
    @6
    eqid
    #
    gsummptres.2
    gsummptres.3
    gsummptres.4
    wph
    vx
    cA
    @0
    cB
    cvv
    cC
    c.0
    @0
    eqid
    gsummptres.3
    gsummptres.4
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsummptres.1
    cG
    c0g
    fvex
    eqeltri
    a1i
    fsuppmptdm
    @1
    @3
    cin
    c0
    wceq
    wph
    cA
    cD
    inindif
    a1i
    cA
    @1
    @3
    cun
    #
    wceq
    wph
    @9
    cA
    cA
    cD
    inundif
    eqcomi
    a1i
    gsumsplit2
    wph
    @7
    @2
    c.0
    @6
    co
    #
    @2
    wph
    @5
    c.0
    @2
    @6
    wph
    @5
    cG
    vx
    @3
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    wph
    @4
    @11
    cG
    cgsu
    wph
    vx
    @3
    cC
    c.0
    gsummptres.5
    mpteq2dva
    oveq2d
    wph
    cG
    cmnd
    wcel
    #
    @3
    cfn
    wcel
    #
    @12
    c.0
    wceq
    wph
    cG
    ccmn
    wcel
    @13
    gsummptres.2
    cG
    cmnmnd
    syl
    #
    wph
    cA
    cfn
    wcel
    #
    @14
    gsummptres.3
    cA
    cD
    diffi
    syl
    @3
    vx
    cG
    cfn
    c.0
    gsummptres.1
    gsumz
    syl2anc
    eqtrd
    oveq2d
    wph
    @13
    @2
    cB
    wcel
    @10
    @2
    wceq
    @15
    wph
    cB
    vx
    cG
    @1
    cC
    gsummptres.0
    gsummptres.2
    wph
    @16
    @1
    cfn
    wcel
    gsummptres.3
    cA
    cD
    infi
    syl
    wph
    cC
    cB
    wcel
    #
    vx
    @1
    vx
    cv
    #
    @1
    wcel
    wph
    @18
    cA
    wcel
    @17
    @1
    cA
    @18
    cA
    cD
    inss1
    sseli
    gsummptres.4
    sylan2
    ralrimiva
    gsummptcl
    cB
    @6
    cG
    @2
    c.0
    gsummptres.0
    @8
    gsummptres.1
    mndrid
    syl2anc
    eqtrd
    eqtrd
end
