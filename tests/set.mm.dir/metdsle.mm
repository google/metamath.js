include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "simprr.mm"
include "simpr.mm"
include "sselda.mm"
include "adantrr.mm"
include "jca.mm"
include "metdstri.mm"
include "syldan.mm"
include "cc0.mm"
include "wceq.mm"
include "simpll.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "metds0.mm"
include "3expa.mm"
include "oveq12d.mm"
include "cxr.mm"
include "xmetcl.mm"
include "xaddid1.mm"
include "syl.mm"
include "eqtrd.mm"
include "breqtrd.mm"

theorem metdsle
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cF: class F
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  let cJ: class J
  let wph: wff ph
  let cC: class C
  let cG: class G
  let cR: class R
  let cT: class T
  let cK: class K
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint B x
  disjoint B y
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
  disjoint y z
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
  assert |- ( ( ( D e. ( *Met ` X ) /\ S C_ X ) /\ ( A e. S /\ B e. X ) ) -> ( F ` B ) <_ ( A D B ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cA
    cS
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    wa
    #
    cB
    cF
    cfv
    #
    cB
    cA
    cD
    co
    #
    cA
    cF
    cfv
    #
    cxad
    co
    #
    cA
    cB
    cD
    co
    #
    cle
    @2
    @5
    @4
    cA
    cX
    wcel
    #
    wa
    @7
    @10
    cle
    wbr
    @6
    @4
    @12
    @2
    @3
    @4
    simprr
    #
    @2
    @3
    @12
    @4
    @2
    cS
    cX
    cA
    @0
    @1
    simpr
    sselda
    adantrr
    #
    jca
    vx
    vy
    cB
    cA
    cD
    cS
    cF
    cX
    metdscn.f
    metdstri
    syldan
    @6
    @10
    @11
    cc0
    cxad
    co
    #
    @11
    @6
    @8
    @11
    @9
    cc0
    cxad
    @6
    @0
    @4
    @12
    @8
    @11
    wceq
    @0
    @1
    @5
    simpll
    #
    @13
    @14
    cB
    cA
    cD
    cX
    xmetsym
    syl3anc
    @2
    @3
    @9
    cc0
    wceq
    #
    @4
    @0
    @1
    @3
    @17
    vx
    vy
    cA
    cD
    cS
    cF
    cX
    metdscn.f
    metds0
    3expa
    adantrr
    oveq12d
    @6
    @11
    cxr
    wcel
    #
    @15
    @11
    wceq
    @6
    @0
    @12
    @4
    @18
    @16
    @14
    @13
    cA
    cB
    cD
    cX
    xmetcl
    syl3anc
    @11
    xaddid1
    syl
    eqtrd
    breqtrd
end
