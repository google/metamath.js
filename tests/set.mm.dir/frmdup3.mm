include "cmnd.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cword.mm"
include "cv.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "cmhm.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "frmdup1.mm"
include "cfv.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "frmdup2.mm"
include "mpteq2dva.mm"
include "cbs.mm"
include "mhmf.mm"
include "syl.mm"
include "vrmdf.mm"
include "3ad2ant2.mm"
include "frmdbas.mm"
include "feq3d.mm"
include "mpbird.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "feqmptd.mm"
include "3eqtr4d.mm"
include "frmdup3lem.mm"
include "expr.mm"
include "ralrimiva.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "eqreu.mm"
include "syl3anc.mm"

theorem frmdup3
  let cA: class A
  let cB: class B
  let cU: class U
  let vm: setvar m
  let cG: class G
  let cI: class I
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume frmdup3.m: |- M = ( freeMnd ` I )
  assume frmdup3.b: |- B = ( Base ` G )
  assume frmdup3.u: |- U = ( varFMnd ` I )

  disjoint A m
  disjoint B m
  disjoint G m
  disjoint I m
  disjoint M m
  disjoint U m
  disjoint V m
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint M x
  disjoint M y
  disjoint F x
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint V y
  assert |- ( ( G e. Mnd /\ I e. V /\ A : I --> B ) -> E! m e. ( M MndHom G ) ( m o. U ) = A )

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
    vx
    cI
    cword
    #
    cG
    cA
    vx
    cv
    ccom
    cgsu
    co
    cmpt
    #
    cM
    cG
    cmhm
    co
    #
    wcel
    #
    @5
    cU
    ccom
    #
    cA
    wceq
    #
    vm
    cv
    #
    cU
    ccom
    #
    cA
    wceq
    #
    @10
    @5
    wceq
    #
    wi
    #
    vm
    @6
    wral
    @12
    vm
    @6
    wreu
    @3
    vx
    cA
    cB
    @5
    cG
    cI
    cM
    cV
    frmdup3.m
    frmdup3.b
    @5
    eqid
    #
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    frmdup1
    #
    @3
    vy
    cI
    vy
    cv
    #
    cU
    cfv
    @5
    cfv
    #
    cmpt
    #
    vy
    cI
    @20
    cA
    cfv
    #
    cmpt
    @8
    cA
    @3
    vy
    cI
    @21
    @23
    @3
    @20
    cI
    wcel
    #
    wa
    vx
    cA
    cB
    cU
    @5
    cG
    cI
    cM
    cV
    @20
    frmdup3.m
    frmdup3.b
    @15
    @3
    @0
    @24
    @16
    adantr
    @3
    @1
    @24
    @17
    adantr
    @3
    @2
    @24
    @18
    adantr
    frmdup3.u
    @3
    @24
    simpr
    frmdup2
    mpteq2dva
    @3
    cM
    cbs
    cfv
    #
    cB
    @5
    wf
    #
    cI
    @25
    cU
    wf
    #
    @8
    @22
    wceq
    @3
    @7
    @26
    @19
    @25
    cB
    cM
    cG
    @5
    @25
    eqid
    #
    frmdup3.b
    mhmf
    syl
    @3
    @27
    cI
    @4
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
    @25
    @4
    cU
    cI
    @1
    @0
    @25
    @4
    wceq
    @2
    @25
    cI
    cM
    cV
    frmdup3.m
    @28
    frmdbas
    3ad2ant2
    feq3d
    mpbird
    vy
    @5
    cU
    cI
    @25
    cB
    fcompt
    syl2anc
    @3
    vy
    cI
    cB
    cA
    @18
    feqmptd
    3eqtr4d
    @3
    @14
    vm
    @6
    @3
    @10
    @6
    wcel
    @12
    @13
    vx
    cA
    cB
    cU
    @10
    cG
    cI
    cM
    cV
    frmdup3.m
    frmdup3.b
    frmdup3.u
    frmdup3lem
    expr
    ralrimiva
    @12
    @9
    vm
    @6
    @5
    @13
    @11
    @8
    cA
    @10
    @5
    cU
    coeq1
    eqeq1d
    eqreu
    syl3anc
end
