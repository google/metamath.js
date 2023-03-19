include "clindf.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "csca.mm"
include "csn.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cbs.mm"
include "clmod.mm"
include "wcel.mm"
include "wf.mm"
include "wb.mm"
include "eqid.mm"
include "islindf4.mm"
include "syl3anc.mm"
include "wa.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "eqeltrd.mm"
include "frlm0.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "bitr4d.mm"
include "clmhm.mm"
include "cghm.mm"
include "frlmup1.mm"
include "lmghm.mm"
include "ghmf1.mm"
include "3syl.mm"

theorem islindf5
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cI: class I
  let cX: class X
  let vy: setvar y
  assume islindf5.f: |- F = ( R freeLMod I )
  assume islindf5.b: |- B = ( Base ` F )
  assume islindf5.c: |- C = ( Base ` T )
  assume islindf5.v: |- .x. = ( .s ` T )
  assume islindf5.e: |- E = ( x e. B |-> ( T gsum ( x oF .x. A ) ) )
  assume islindf5.t: |- ( ph -> T e. LMod )
  assume islindf5.i: |- ( ph -> I e. X )
  assume islindf5.r: |- ( ph -> R = ( Scalar ` T ) )
  assume islindf5.a: |- ( ph -> A : I --> C )

  disjoint ph x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint I x
  disjoint R x
  disjoint T x
  disjoint .x. x
  disjoint X x
  disjoint ph y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint E y
  disjoint F y
  disjoint I y
  disjoint T y
  disjoint .x. y
  disjoint X y
  assert |- ( ph -> ( A LIndF T <-> E : B -1-1-> C ) )

  proof
    wph
    cA
    cT
    clindf
    wbr
    #
    vy
    cv
    #
    cE
    cfv
    #
    cT
    c0g
    cfv
    #
    wceq
    #
    @1
    cF
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    cB
    cC
    cE
    wf1
    #
    wph
    @0
    cT
    @1
    cA
    c.x
    cof
    #
    co
    #
    cgsu
    co
    #
    @3
    wceq
    #
    @1
    cI
    cT
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    #
    cxp
    #
    wceq
    #
    wi
    #
    vy
    @14
    cI
    cfrlm
    co
    #
    cbs
    cfv
    #
    wral
    #
    @8
    wph
    cT
    clmod
    wcel
    #
    cI
    cX
    wcel
    #
    cI
    cC
    cA
    wf
    @0
    @22
    wb
    islindf5.t
    islindf5.i
    islindf5.a
    vy
    cC
    @14
    c.x
    cA
    cI
    @21
    cT
    cX
    @15
    @3
    islindf5.c
    @14
    eqid
    #
    islindf5.v
    @3
    eqid
    #
    @15
    eqid
    @21
    eqid
    islindf4
    syl3anc
    wph
    @8
    @19
    vy
    cB
    wral
    @22
    wph
    @7
    @19
    vy
    cB
    wph
    @1
    cB
    wcel
    #
    wa
    #
    @4
    @13
    @6
    @18
    @28
    @2
    @12
    @3
    @27
    @2
    @12
    wceq
    wph
    vx
    @1
    cT
    vx
    cv
    #
    cA
    @10
    co
    #
    cgsu
    co
    @12
    cB
    cE
    @29
    @1
    wceq
    @30
    @11
    cT
    cgsu
    @29
    @1
    cA
    @10
    oveq1
    oveq2d
    islindf5.e
    cT
    @11
    cgsu
    ovex
    fvmpt
    adantl
    eqeq1d
    @28
    @5
    @17
    @1
    wph
    @5
    @17
    wceq
    @27
    wph
    cI
    cR
    c0g
    cfv
    #
    csn
    #
    cxp
    #
    @5
    @17
    wph
    cR
    crg
    wcel
    @24
    @33
    @5
    wceq
    wph
    cR
    @14
    crg
    islindf5.r
    wph
    @23
    @14
    crg
    wcel
    islindf5.t
    @14
    cT
    @25
    lmodring
    syl
    eqeltrd
    islindf5.i
    cR
    cF
    cI
    cX
    @31
    islindf5.f
    @31
    eqid
    frlm0
    syl2anc
    wph
    @32
    @16
    cI
    wph
    @31
    @15
    wph
    cR
    @14
    c0g
    islindf5.r
    fveq2d
    sneqd
    xpeq2d
    eqtr3d
    adantr
    eqeq2d
    imbi12d
    ralbidva
    wph
    @19
    vy
    @21
    cB
    wph
    @21
    cF
    cbs
    cfv
    cB
    wph
    @20
    cF
    cbs
    wph
    @20
    cR
    cI
    cfrlm
    co
    cF
    wph
    @14
    cR
    cI
    cfrlm
    wph
    cR
    @14
    islindf5.r
    eqcomd
    oveq1d
    islindf5.f
    syl6eqr
    fveq2d
    islindf5.b
    syl6eqr
    raleqdv
    bitr4d
    bitr4d
    wph
    cE
    cF
    cT
    clmhm
    co
    wcel
    cE
    cF
    cT
    cghm
    co
    wcel
    @9
    @8
    wb
    wph
    vx
    cA
    cB
    cC
    cR
    cT
    c.x
    cE
    cF
    cI
    cX
    islindf5.f
    islindf5.b
    islindf5.c
    islindf5.v
    islindf5.e
    islindf5.t
    islindf5.i
    islindf5.r
    islindf5.a
    frlmup1
    cF
    cT
    cE
    lmghm
    vy
    cF
    cT
    @3
    cE
    cB
    cC
    @5
    islindf5.b
    islindf5.c
    @5
    eqid
    @26
    ghmf1
    3syl
    bitr4d
end
