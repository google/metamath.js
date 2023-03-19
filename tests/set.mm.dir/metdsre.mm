include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "wfn.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxmt.mm"
include "metxmet.mm"
include "metdsf.mm"
include "sylan.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "simpll.mm"
include "simpr.mm"
include "sselda.mm"
include "adantrr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "simprbi.mm"
include "metdsle.mm"
include "sylanl1.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem metdsre
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let cF: class F
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vs: setvar s
  let vt: setvar t
  let cJ: class J
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cG: class G
  let cR: class R
  let cT: class T
  let cK: class K
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint r s
  disjoint r t
  disjoint D r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint D s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint D w
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint B x
  disjoint B y
  disjoint C r
  disjoint C s
  disjoint C w
  disjoint C z
  disjoint G s
  disjoint G t
  disjoint R w
  disjoint R z
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X z
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  assert |- ( ( D e. ( Met ` X ) /\ S C_ X /\ S =/= (/) ) -> F : X --> RR )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    cS
    c0
    wne
    #
    cX
    cr
    cF
    wf
    #
    @2
    vz
    cv
    #
    cS
    wcel
    #
    vz
    wex
    @0
    @1
    wa
    #
    @3
    vz
    cS
    n0
    @6
    @5
    @3
    vz
    @6
    @5
    @3
    @6
    @5
    wa
    #
    cF
    cX
    wfn
    #
    vw
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    vw
    cX
    wral
    @3
    @7
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @8
    @6
    @13
    @5
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @1
    @13
    cD
    cX
    metxmet
    #
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    sylan
    #
    adantr
    cX
    @12
    cF
    ffn
    syl
    @7
    @11
    vw
    cX
    @6
    @5
    @9
    cX
    wcel
    #
    @11
    @6
    @5
    @17
    wa
    #
    wa
    #
    @10
    cxr
    wcel
    #
    @4
    @9
    cD
    co
    #
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    @10
    @21
    cle
    wbr
    #
    @11
    @19
    @10
    @12
    wcel
    #
    @20
    @19
    cX
    @12
    @9
    cF
    @6
    @13
    @18
    @16
    adantr
    @6
    @5
    @17
    simprr
    #
    ffvelrnd
    #
    @25
    @20
    @23
    @10
    elxrge0
    #
    simplbi
    syl
    @19
    @0
    @4
    cX
    wcel
    #
    @17
    @22
    @0
    @1
    @18
    simpll
    @6
    @5
    @29
    @17
    @6
    cS
    cX
    @4
    @0
    @1
    simpr
    sselda
    adantrr
    @26
    @4
    @9
    cD
    cX
    metcl
    syl3anc
    @19
    @25
    @23
    @27
    @25
    @20
    @23
    @28
    simprbi
    syl
    @0
    @14
    @1
    @18
    @24
    @15
    vx
    vy
    @4
    @9
    cD
    cS
    cF
    cX
    metdscn.f
    metdsle
    sylanl1
    @10
    @21
    xrrege0
    syl22anc
    anassrs
    ralrimiva
    vw
    cX
    cr
    cF
    ffnfv
    sylanbrc
    ex
    exlimdv
    syl5bi
    3impia
end
