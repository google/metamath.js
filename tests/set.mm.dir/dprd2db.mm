include "cdprd.mm"
include "co.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cres.mm"
include "cima.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "cdm.mm"
include "wbr.mm"
include "wceq.mm"
include "dprd2da.mm"
include "dprdspan.mm"
include "syl.mm"
include "wrel.mm"
include "wss.mm"
include "relssres.mm"
include "syl2anc.mm"
include "imaeq2d.mm"
include "csubg.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "fnima.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "unieqd.mm"
include "fveq2d.mm"
include "ssid.mm"
include "a1i.mm"
include "dprd2dlem1.mm"
include "3eqtrd.mm"

theorem dprd2db
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cI: class I
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cX: class X
  assume dprd2d.1: |- ( ph -> Rel A )
  assume dprd2d.2: |- ( ph -> S : A --> ( SubGrp ` G ) )
  assume dprd2d.3: |- ( ph -> dom A C_ I )
  assume dprd2d.4: |- ( ( ph /\ i e. I ) -> G dom DProd ( j e. ( A " { i } ) |-> ( i S j ) ) )
  assume dprd2d.5: |- ( ph -> G dom DProd ( i e. I |-> ( G DProd ( j e. ( A " { i } ) |-> ( i S j ) ) ) ) )
  assume dprd2d.k: |- K = ( mrCls ` ( SubGrp ` G ) )

  disjoint i j
  disjoint A i
  disjoint A j
  disjoint G i
  disjoint G j
  disjoint I i
  disjoint K i
  disjoint i ph
  disjoint j ph
  disjoint S i
  disjoint S j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C i
  disjoint C k
  disjoint C x
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint K k
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint X i
  disjoint X j
  assert |- ( ph -> ( G DProd S ) = ( G DProd ( i e. I |-> ( G DProd ( j e. ( A " { i } ) |-> ( i S j ) ) ) ) ) )

  proof
    wph
    cG
    cS
    cdprd
    co
    #
    cS
    crn
    #
    cuni
    #
    cK
    cfv
    #
    cS
    cA
    cI
    cres
    #
    cima
    #
    cuni
    #
    cK
    cfv
    cG
    vi
    cI
    cG
    vj
    cA
    vi
    cv
    #
    csn
    cima
    @7
    vj
    cv
    cS
    co
    cmpt
    cdprd
    co
    cmpt
    cdprd
    co
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    @0
    @3
    wceq
    wph
    cA
    cS
    vi
    vj
    cG
    cI
    cK
    dprd2d.1
    dprd2d.2
    dprd2d.3
    dprd2d.4
    dprd2d.5
    dprd2d.k
    dprd2da
    cS
    cG
    cK
    dprd2d.k
    dprdspan
    syl
    wph
    @2
    @6
    cK
    wph
    @1
    @5
    wph
    @5
    cS
    cA
    cima
    #
    @1
    wph
    @4
    cA
    cS
    wph
    cA
    wrel
    cA
    cdm
    cI
    wss
    @4
    cA
    wceq
    dprd2d.1
    dprd2d.3
    cA
    cI
    relssres
    syl2anc
    imaeq2d
    wph
    cA
    cG
    csubg
    cfv
    #
    cS
    wf
    cS
    cA
    wfn
    @8
    @1
    wceq
    dprd2d.2
    cA
    @9
    cS
    ffn
    cA
    cS
    fnima
    3syl
    eqtr2d
    unieqd
    fveq2d
    wph
    cA
    cI
    cS
    vi
    vj
    cG
    cI
    cK
    dprd2d.1
    dprd2d.2
    dprd2d.3
    dprd2d.4
    dprd2d.5
    dprd2d.k
    cI
    cI
    wss
    wph
    cI
    ssid
    a1i
    dprd2dlem1
    3eqtrd
end
