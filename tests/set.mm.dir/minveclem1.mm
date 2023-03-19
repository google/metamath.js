include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cngp.mm"
include "ccph.mm"
include "cphngp.mm"
include "syl.mm"
include "adantr.mm"
include "clmod.mm"
include "cphlmod.mm"
include "clss.mm"
include "eqid.mm"
include "lssss.mm"
include "sselda.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "frn.mm"
include "syl5eqss.mm"
include "lssn0.mm"
include "wceq.mm"
include "cdm.mm"
include "eqeq1i.mm"
include "dm0rn0.mm"
include "fvex.mm"
include "dmmpti.mm"
include "3bitr2i.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "nmge0.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "raleqi.mm"
include "3jca.mm"

theorem minveclem1
  let wph: wff ph
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cU: class U
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cK: class K
  let cD: class D
  let cS: class S
  let cT: class T
  let cL: class L
  assume minvec.x: |- X = ( Base ` U )
  assume minvec.m: |- .- = ( -g ` U )
  assume minvec.n: |- N = ( norm ` U )
  assume minvec.u: |- ( ph -> U e. CPreHil )
  assume minvec.y: |- ( ph -> Y e. ( LSubSp ` U ) )
  assume minvec.w: |- ( ph -> ( U |`s Y ) e. CMetSp )
  assume minvec.a: |- ( ph -> A e. X )
  assume minvec.j: |- J = ( TopOpen ` U )
  assume minvec.r: |- R = ran ( y e. Y |-> ( N ` ( A .- y ) ) )

  disjoint w y
  disjoint .- w
  disjoint .- y
  disjoint A w
  disjoint A y
  disjoint J w
  disjoint J y
  disjoint N w
  disjoint N y
  disjoint ph w
  disjoint ph y
  disjoint R w
  disjoint R y
  disjoint U w
  disjoint U y
  disjoint X w
  disjoint X y
  disjoint Y w
  disjoint Y y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint .- j
  disjoint w x
  disjoint x y
  disjoint .- x
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j z
  disjoint A j
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint J r
  disjoint J x
  disjoint P x
  disjoint P y
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint N j
  disjoint N x
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint R x
  disjoint U x
  disjoint X r
  disjoint X x
  disjoint Y j
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y x
  disjoint Y z
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ph -> ( R C_ RR /\ R =/= (/) /\ A. w e. R 0 <_ w ) )

  proof
    wph
    cR
    cr
    wss
    cR
    c0
    wne
    #
    cc0
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    cR
    vy
    cY
    cA
    vy
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    minvec.r
    wph
    cY
    cr
    @7
    wf
    @8
    cr
    wss
    wph
    vy
    cY
    @6
    cr
    @7
    wph
    @4
    cY
    wcel
    #
    wa
    #
    cU
    cngp
    wcel
    #
    @5
    cX
    wcel
    #
    @6
    cr
    wcel
    wph
    @11
    @9
    wph
    cU
    ccph
    wcel
    #
    @11
    minvec.u
    cU
    cphngp
    syl
    adantr
    #
    @10
    cU
    clmod
    wcel
    #
    cA
    cX
    wcel
    #
    @4
    cX
    wcel
    @12
    wph
    @15
    @9
    wph
    @13
    @15
    minvec.u
    cU
    cphlmod
    syl
    adantr
    wph
    @16
    @9
    minvec.a
    adantr
    wph
    cY
    cX
    @4
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    minvec.y
    @17
    cY
    cX
    cU
    minvec.x
    @17
    eqid
    #
    lssss
    syl
    sselda
    c.mi
    cX
    cU
    cA
    @4
    minvec.x
    minvec.m
    lmodvsubcl
    syl3anc
    #
    @5
    cU
    cN
    cX
    minvec.x
    minvec.n
    nmcl
    syl2anc
    @7
    eqid
    #
    fmptd
    cY
    cr
    @7
    frn
    syl
    syl5eqss
    wph
    cY
    c0
    wne
    #
    @0
    wph
    @18
    @22
    minvec.y
    @17
    cY
    cU
    @19
    lssn0
    syl
    cR
    c0
    cY
    c0
    cR
    c0
    wceq
    @8
    c0
    wceq
    @7
    cdm
    #
    c0
    wceq
    cY
    c0
    wceq
    cR
    @8
    c0
    minvec.r
    eqeq1i
    @7
    dm0rn0
    @23
    cY
    c0
    vy
    cY
    @6
    @7
    @5
    cN
    fvex
    #
    @21
    dmmpti
    eqeq1i
    3bitr2i
    necon3bii
    sylibr
    wph
    @2
    vw
    @8
    wral
    #
    @3
    wph
    cc0
    @6
    cle
    wbr
    #
    vy
    cY
    wral
    #
    @25
    wph
    @26
    vy
    cY
    @10
    @11
    @12
    @26
    @14
    @20
    @5
    cU
    cN
    cX
    minvec.x
    minvec.n
    nmge0
    syl2anc
    ralrimiva
    @6
    cvv
    wcel
    #
    vy
    cY
    wral
    @25
    @27
    wb
    @28
    vy
    cY
    @24
    rgenw
    @2
    @26
    vy
    vw
    cY
    @6
    @7
    cvv
    @21
    @1
    @6
    cc0
    cle
    breq2
    ralrnmpt
    ax-mp
    sylibr
    @2
    vw
    cR
    @8
    minvec.r
    raleqi
    sylibr
    3jca
end
