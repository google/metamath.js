include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "cbl.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "cle.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "metdsf.mm"
include "3adant3.mm"
include "ssel2.mm"
include "3adant1.mm"
include "ffvelrnd.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "syl.mm"
include "xrleid.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "metdsge.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "wne.mm"
include "wa.mm"
include "simpl3.mm"
include "adantr.mm"
include "simpr.mm"
include "xblcntr.mm"
include "syl112anc.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "ex.mm"
include "necon2bd.mm"
include "mpd.mm"
include "wo.mm"
include "simprbi.mm"
include "0xr.mm"
include "xrleloe.mm"
include "sylancr.mm"
include "ord.mm"
include "eqcomd.mm"

theorem metds0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
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
  disjoint A x
  disjoint A y
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
  assert |- ( ( D e. ( *Met ` X ) /\ S C_ X /\ A e. S ) -> ( F ` A ) = 0 )

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
    cA
    cS
    wcel
    #
    w3a
    #
    cc0
    cA
    cF
    cfv
    #
    @3
    cc0
    @4
    clt
    wbr
    #
    wn
    #
    cc0
    @4
    wceq
    #
    @3
    cS
    cA
    @4
    cD
    cbl
    cfv
    co
    #
    cin
    #
    c0
    wceq
    #
    @6
    @3
    @4
    @4
    cle
    wbr
    #
    @10
    @3
    @4
    cxr
    wcel
    #
    @11
    @3
    @4
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @12
    @3
    cX
    @13
    cA
    cF
    @0
    @1
    cX
    @13
    cF
    wf
    @2
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    3adant3
    @1
    @2
    cA
    cX
    wcel
    #
    @0
    cS
    cX
    cA
    ssel2
    3adant1
    #
    ffvelrnd
    #
    @14
    @12
    cc0
    @4
    cle
    wbr
    #
    @4
    elxrge0
    #
    simplbi
    syl
    #
    @4
    xrleid
    syl
    @3
    @0
    @1
    @15
    @12
    @11
    @10
    wb
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    @16
    @20
    vx
    vy
    cA
    cD
    @4
    cS
    cF
    cX
    metdscn.f
    metdsge
    syl31anc
    mpbid
    @3
    @5
    @9
    c0
    @3
    @5
    @9
    c0
    wne
    #
    @3
    @5
    wa
    #
    @2
    cA
    @8
    wcel
    #
    @22
    @0
    @1
    @2
    @5
    simpl3
    @23
    @0
    @15
    @12
    @5
    @24
    @3
    @0
    @5
    @21
    adantr
    @3
    @15
    @5
    @16
    adantr
    @3
    @12
    @5
    @20
    adantr
    @3
    @5
    simpr
    cD
    cA
    @4
    cX
    xblcntr
    syl112anc
    cA
    cS
    @8
    inelcm
    syl2anc
    ex
    necon2bd
    mpd
    @3
    @5
    @7
    @3
    @18
    @5
    @7
    wo
    #
    @3
    @14
    @18
    @17
    @14
    @12
    @18
    @19
    simprbi
    syl
    @3
    cc0
    cxr
    wcel
    @12
    @18
    @25
    wb
    0xr
    @20
    cc0
    @4
    xrleloe
    sylancr
    mpbid
    ord
    mpd
    eqcomd
end
