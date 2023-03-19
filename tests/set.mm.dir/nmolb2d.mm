include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "anassrs.mm"
include "cc0.mm"
include "0le0.mm"
include "recnd.mm"
include "mul01d.mm"
include "syl5breqr.mm"
include "c0g.mm"
include "cghm.mm"
include "eqid.mm"
include "ghmid.mm"
include "syl.mm"
include "cngp.mm"
include "nm0.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "adantr.mm"
include "pm2.61ne.mm"
include "ralrimiva.mm"
include "cr.mm"
include "wi.mm"
include "nmolb.mm"
include "syl311anc.mm"
include "mpd.mm"

theorem nmolb2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )
  assume nmofval.2: |- V = ( Base ` S )
  assume nmofval.3: |- L = ( norm ` S )
  assume nmofval.4: |- M = ( norm ` T )
  assume nmolb2d.z: |- .0. = ( 0g ` S )
  assume nmolb2d.1: |- ( ph -> S e. NrmGrp )
  assume nmolb2d.2: |- ( ph -> T e. NrmGrp )
  assume nmolb2d.3: |- ( ph -> F e. ( S GrpHom T ) )
  assume nmolb2d.4: |- ( ph -> A e. RR )
  assume nmolb2d.5: |- ( ph -> 0 <_ A )
  assume nmolb2d.6: |- ( ( ph /\ ( x e. V /\ x =/= .0. ) ) -> ( M ` ( F ` x ) ) <_ ( A x. ( L ` x ) ) )

  disjoint L x
  disjoint M x
  disjoint S x
  disjoint T x
  disjoint A x
  disjoint F x
  disjoint ph x
  disjoint V x
  disjoint N x
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint L f
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint L r
  disjoint s t
  disjoint s x
  disjoint L s
  disjoint t x
  disjoint L t
  disjoint M f
  disjoint M r
  disjoint M s
  disjoint M t
  disjoint S f
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint T f
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint A r
  disjoint A s
  disjoint F f
  disjoint F r
  disjoint F s
  disjoint V f
  disjoint V r
  disjoint V s
  disjoint V t
  disjoint X r
  disjoint X x
  disjoint N r
  disjoint N s
  disjoint N t
  assert |- ( ph -> ( N ` F ) <_ A )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cM
    cfv
    #
    cA
    @0
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    cV
    wral
    #
    cF
    cN
    cfv
    cA
    cle
    wbr
    #
    wph
    @5
    vx
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    @5
    c.0
    cF
    cfv
    #
    cM
    cfv
    #
    cA
    c.0
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    c.0
    @0
    c.0
    wceq
    #
    @2
    @10
    @4
    @12
    cle
    @14
    @1
    @9
    cM
    @0
    c.0
    cF
    fveq2
    fveq2d
    @14
    @3
    @11
    cA
    cmul
    @0
    c.0
    cL
    fveq2
    oveq2d
    breq12d
    wph
    @8
    @0
    c.0
    wne
    @5
    nmolb2d.6
    anassrs
    wph
    @13
    @8
    wph
    cc0
    cA
    cc0
    cmul
    co
    #
    @10
    @12
    cle
    wph
    cc0
    cc0
    @15
    cle
    0le0
    wph
    cA
    wph
    cA
    nmolb2d.4
    recnd
    mul01d
    syl5breqr
    wph
    @10
    cT
    c0g
    cfv
    #
    cM
    cfv
    #
    cc0
    wph
    @9
    @16
    cM
    wph
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @9
    @16
    wceq
    nmolb2d.3
    cS
    cT
    cF
    c.0
    @16
    nmolb2d.z
    @16
    eqid
    #
    ghmid
    syl
    fveq2d
    wph
    cT
    cngp
    wcel
    #
    @17
    cc0
    wceq
    nmolb2d.2
    cT
    cM
    @16
    nmofval.4
    @19
    nm0
    syl
    eqtrd
    wph
    @11
    cc0
    cA
    cmul
    wph
    cS
    cngp
    wcel
    #
    @11
    cc0
    wceq
    nmolb2d.1
    cS
    cL
    c.0
    nmofval.3
    nmolb2d.z
    nm0
    syl
    oveq2d
    3brtr4d
    adantr
    pm2.61ne
    ralrimiva
    wph
    @21
    @20
    @18
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    @6
    @7
    wi
    nmolb2d.1
    nmolb2d.2
    nmolb2d.3
    nmolb2d.4
    nmolb2d.5
    vx
    cA
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    nmofval.1
    nmofval.2
    nmofval.3
    nmofval.4
    nmolb
    syl311anc
    mpd
end
