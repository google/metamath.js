include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cfv.mm"
include "ccom.mm"
include "climc.mm"
include "co.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "expr.mm"
include "necon1bd.mm"
include "cc.mm"
include "wb.mm"
include "limccl.mm"
include "sseldi.mm"
include "adantr.mm"
include "elsn2g.mm"
include "syl.mm"
include "sylibrd.mm"
include "orrd.mm"
include "elun.mm"
include "sylibr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdm.mm"
include "dmmptd.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "limcrcl.mm"
include "simp2d.mm"
include "eqsstr3d.mm"
include "snssd.mm"
include "unssd.mm"
include "ccnp.mm"
include "limcmpt.mm"
include "mpbid.mm"
include "limccnp.mm"
include "ssun2.mm"
include "snssg.mm"
include "mpbiri.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "fmptco.mm"
include "ifid.mm"
include "anassrs.mm"
include "ifeq1da.mm"
include "syl5reqr.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eltr3d.mm"

theorem limcco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cX: class X
  assume limcco.r: |- ( ( ph /\ ( x e. A /\ R =/= C ) ) -> R e. B )
  assume limcco.s: |- ( ( ph /\ y e. B ) -> S e. CC )
  assume limcco.c: |- ( ph -> C e. ( ( x e. A |-> R ) limCC X ) )
  assume limcco.d: |- ( ph -> D e. ( ( y e. B |-> S ) limCC C ) )
  assume limcco.1: |- ( y = R -> S = T )
  assume limcco.2: |- ( ( ph /\ ( x e. A /\ R = C ) ) -> T = D )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint R y
  disjoint S x
  disjoint T y
  assert |- ( ph -> D e. ( ( x e. A |-> T ) limCC X ) )

  proof
    wph
    cC
    vy
    cB
    cC
    csn
    #
    cun
    #
    vy
    cv
    #
    cC
    wceq
    #
    cD
    cS
    cif
    #
    cmpt
    #
    cfv
    #
    @5
    vx
    cA
    cR
    cmpt
    #
    ccom
    #
    cX
    climc
    co
    cD
    vx
    cA
    cT
    cmpt
    #
    cX
    climc
    co
    wph
    cA
    cX
    cC
    @1
    @7
    @5
    ccnfld
    ctopn
    cfv
    #
    @1
    crest
    co
    #
    @10
    wph
    vx
    cA
    cR
    @1
    @7
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    cR
    cB
    wcel
    #
    cR
    @0
    wcel
    #
    wo
    cR
    @1
    wcel
    @13
    @14
    @15
    @13
    @14
    wn
    cR
    cC
    wceq
    #
    @15
    @13
    @14
    cR
    cC
    wph
    @12
    cR
    cC
    wne
    @14
    limcco.r
    expr
    necon1bd
    @13
    cC
    cc
    wcel
    #
    @15
    @16
    wb
    wph
    @17
    @12
    wph
    @7
    cX
    climc
    co
    #
    cc
    cC
    cX
    @7
    limccl
    limcco.c
    sseldi
    #
    adantr
    cR
    cC
    cc
    elsn2g
    syl
    sylibrd
    orrd
    cR
    cB
    @0
    elun
    sylibr
    #
    @7
    eqid
    fmptd
    wph
    cB
    @0
    cc
    wph
    cB
    vy
    cB
    cS
    cmpt
    #
    cdm
    #
    cc
    wph
    vy
    @21
    cB
    cS
    cc
    @21
    eqid
    limcco.s
    dmmptd
    wph
    @22
    cc
    @21
    wf
    #
    @22
    cc
    wss
    #
    @17
    wph
    cD
    @21
    cC
    climc
    co
    #
    wcel
    #
    @23
    @24
    @17
    w3a
    limcco.d
    cC
    cD
    @21
    limcrcl
    syl
    simp2d
    eqsstr3d
    #
    wph
    cC
    cc
    @19
    snssd
    unssd
    @10
    eqid
    #
    @11
    eqid
    #
    limcco.c
    wph
    @26
    @5
    cC
    @11
    @10
    ccnp
    co
    cfv
    wcel
    limcco.d
    wph
    vy
    cB
    cC
    cD
    cS
    @11
    @10
    @27
    @19
    limcco.s
    @29
    @28
    limcmpt
    mpbid
    limccnp
    wph
    cC
    @1
    wcel
    #
    @26
    @6
    cD
    wceq
    wph
    @30
    @0
    @1
    wss
    #
    @0
    cB
    ssun2
    wph
    cC
    @18
    wcel
    @30
    @31
    wb
    limcco.c
    cC
    @1
    @18
    snssg
    syl
    mpbiri
    limcco.d
    vy
    cC
    @4
    cD
    @1
    @25
    @5
    @3
    cD
    cS
    iftrue
    @5
    eqid
    fvmptg
    syl2anc
    wph
    @8
    @9
    cX
    climc
    wph
    @8
    vx
    cA
    @16
    cD
    cT
    cif
    #
    cmpt
    @9
    wph
    vx
    vy
    cA
    @1
    cR
    @4
    @32
    @7
    @5
    @20
    wph
    @7
    eqidd
    wph
    @5
    eqidd
    @2
    cR
    wceq
    @3
    @16
    cS
    cT
    cD
    @2
    cR
    cC
    eqeq1
    limcco.1
    ifbieq2d
    fmptco
    wph
    vx
    cA
    @32
    cT
    @13
    cT
    @16
    cT
    cT
    cif
    @32
    @16
    cT
    ifid
    @13
    @16
    cT
    cD
    cT
    wph
    @12
    @16
    cT
    cD
    wceq
    limcco.2
    anassrs
    ifeq1da
    syl5reqr
    mpteq2dva
    eqtrd
    oveq1d
    3eltr3d
end
