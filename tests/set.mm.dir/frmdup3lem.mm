include "cmnd.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cmhm.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "eqid.mm"
include "mhmf.mm"
include "ad2antrl.mm"
include "frmdbas.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "simplrl.mm"
include "simpr.mm"
include "vrmdf.mm"
include "feq3d.mm"
include "mpbird.mm"
include "ad2antrr.mm"
include "wrdco.mm"
include "syl2anc.mm"
include "gsumwmhm.mm"
include "simpll2.mm"
include "frmdgsum.mm"
include "fveq2d.mm"
include "coass.mm"
include "simplrr.mm"
include "coeq1d.mm"
include "syl5eqr.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem frmdup3lem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vy: setvar y
  assume frmdup3.m: |- M = ( freeMnd ` I )
  assume frmdup3.b: |- B = ( Base ` G )
  assume frmdup3.u: |- U = ( varFMnd ` I )

  disjoint A x
  disjoint B x
  disjoint G x
  disjoint I x
  disjoint M x
  disjoint F x
  disjoint U x
  disjoint V x
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint G m
  disjoint G y
  disjoint I m
  disjoint I y
  disjoint M m
  disjoint M y
  disjoint U m
  disjoint U y
  disjoint V m
  disjoint V y
  assert |- ( ( ( G e. Mnd /\ I e. V /\ A : I --> B ) /\ ( F e. ( M MndHom G ) /\ ( F o. U ) = A ) ) -> F = ( x e. Word I |-> ( G gsum ( A o. x ) ) ) )

  proof
    cG
    cmnd
    wcel
    #
    cI
    cV
    wcel
    #
    cI
    cB
    cA
    wf
    #
    w3a
    #
    cF
    cM
    cG
    cmhm
    co
    wcel
    #
    cF
    cU
    ccom
    #
    cA
    wceq
    #
    wa
    #
    wa
    #
    cF
    vx
    cI
    cword
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    vx
    @9
    cG
    cA
    @10
    ccom
    #
    cgsu
    co
    #
    cmpt
    @8
    vx
    @9
    cB
    cF
    @8
    cM
    cbs
    cfv
    #
    cB
    cF
    wf
    #
    @9
    cB
    cF
    wf
    @4
    @15
    @3
    @6
    @14
    cB
    cM
    cG
    cF
    @14
    eqid
    #
    frmdup3.b
    mhmf
    ad2antrl
    @8
    @14
    @9
    cB
    cF
    @3
    @14
    @9
    wceq
    #
    @7
    @1
    @0
    @17
    @2
    @14
    cI
    cM
    cV
    frmdup3.m
    @16
    frmdbas
    3ad2ant2
    #
    adantr
    feq2d
    mpbid
    feqmptd
    @8
    vx
    @9
    @11
    @13
    @8
    @10
    @9
    wcel
    #
    wa
    #
    cM
    cU
    @10
    ccom
    #
    cgsu
    co
    #
    cF
    cfv
    #
    cG
    cF
    @21
    ccom
    #
    cgsu
    co
    #
    @11
    @13
    @20
    @4
    @21
    @14
    cword
    wcel
    #
    @23
    @25
    wceq
    @3
    @4
    @6
    @19
    simplrl
    @20
    @19
    cI
    @14
    cU
    wf
    #
    @26
    @8
    @19
    simpr
    #
    @3
    @27
    @7
    @19
    @3
    @27
    cI
    @9
    cU
    wf
    #
    @1
    @0
    @29
    @2
    cU
    cI
    cV
    frmdup3.u
    vrmdf
    3ad2ant2
    @3
    @14
    @9
    cU
    cI
    @18
    feq3d
    mpbird
    ad2antrr
    cI
    @14
    cU
    @10
    wrdco
    syl2anc
    @14
    cF
    cM
    cG
    @21
    @16
    gsumwmhm
    syl2anc
    @20
    @22
    @10
    cF
    @20
    @1
    @19
    @22
    @10
    wceq
    @0
    @1
    @2
    @7
    @19
    simpll2
    @28
    cU
    cI
    cM
    cV
    @10
    frmdup3.m
    frmdup3.u
    frmdgsum
    syl2anc
    fveq2d
    @20
    @24
    @12
    cG
    cgsu
    @20
    @24
    @5
    @10
    ccom
    @12
    cF
    cU
    @10
    coass
    @20
    @5
    cA
    @10
    @3
    @4
    @6
    @19
    simplrr
    coeq1d
    syl5eqr
    oveq2d
    3eqtr3d
    mpteq2dva
    eqtrd
end
