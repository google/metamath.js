include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cxr.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "wral.mm"
include "cbl.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simpl3.mm"
include "metdsval.mm"
include "syl.mm"
include "breq2d.mm"
include "wb.mm"
include "wf.mm"
include "simpll1.mm"
include "adantr.mm"
include "simpl2.mm"
include "sselda.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "frn.mm"
include "simpr.mm"
include "infxrgelb.mm"
include "syl2anc.mm"
include "wn.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "xrltnle.mm"
include "bitrd.mm"
include "con2bid.mm"
include "ralbidva.mm"
include "cvv.mm"
include "ovex.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "disj.mm"
include "3bitr4g.mm"
include "3bitrd.mm"

theorem metdsge
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
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
  assert |- ( ( ( D e. ( *Met ` X ) /\ S C_ X /\ A e. X ) /\ R e. RR* ) -> ( R <_ ( F ` A ) <-> ( S i^i ( A ( ball ` D ) R ) ) = (/) ) )

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
    cX
    wcel
    #
    w3a
    #
    cR
    cxr
    wcel
    #
    wa
    #
    cR
    cA
    cF
    cfv
    #
    cle
    wbr
    cR
    vy
    cS
    cA
    vy
    cv
    #
    cD
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    cR
    vz
    cv
    #
    cle
    wbr
    #
    vz
    @10
    wral
    #
    cS
    cA
    cR
    cD
    cbl
    cfv
    co
    #
    cin
    c0
    wceq
    #
    @5
    @6
    @11
    cR
    cle
    @5
    @2
    @6
    @11
    wceq
    @0
    @1
    @2
    @4
    simpl3
    #
    vx
    vy
    cA
    cD
    cS
    cF
    cX
    metdscn.f
    metdsval
    syl
    breq2d
    @5
    @10
    cxr
    wss
    #
    @4
    @12
    @15
    wb
    @5
    cS
    cxr
    @9
    wf
    @19
    @5
    vw
    cS
    cA
    vw
    cv
    #
    cD
    co
    #
    cxr
    @9
    @5
    @20
    cS
    wcel
    #
    wa
    #
    @0
    @2
    @20
    cX
    wcel
    #
    @21
    cxr
    wcel
    #
    @0
    @1
    @2
    @4
    @22
    simpll1
    #
    @5
    @2
    @22
    @18
    adantr
    #
    @5
    cS
    cX
    @20
    @0
    @1
    @2
    @4
    simpl2
    sselda
    #
    cA
    @20
    cD
    cX
    xmetcl
    syl3anc
    #
    vy
    vw
    cS
    @8
    @21
    @7
    @20
    cA
    cD
    oveq2
    cbvmptv
    #
    fmptd
    cS
    cxr
    @9
    frn
    syl
    @3
    @4
    simpr
    #
    vz
    @10
    cR
    infxrgelb
    syl2anc
    @5
    cR
    @21
    cle
    wbr
    #
    vw
    cS
    wral
    #
    @20
    @16
    wcel
    #
    wn
    #
    vw
    cS
    wral
    @15
    @17
    @5
    @32
    @35
    vw
    cS
    @23
    @34
    @32
    @23
    @34
    @21
    cR
    clt
    wbr
    #
    @32
    wn
    #
    @23
    @0
    @4
    @2
    @24
    @34
    @36
    wb
    @26
    @5
    @4
    @22
    @31
    adantr
    #
    @27
    @28
    @20
    cD
    cA
    cR
    cX
    elbl2
    syl22anc
    @23
    @25
    @4
    @36
    @37
    wb
    @29
    @38
    @21
    cR
    xrltnle
    syl2anc
    bitrd
    con2bid
    ralbidva
    @21
    cvv
    wcel
    #
    vw
    cS
    wral
    @15
    @33
    wb
    @39
    vw
    cS
    cA
    @20
    cD
    ovex
    rgenw
    @14
    @32
    vw
    vz
    cS
    @21
    @9
    cvv
    @30
    @13
    @21
    cR
    cle
    breq2
    ralrnmpt
    ax-mp
    vw
    cS
    @16
    disj
    3bitr4g
    3bitrd
end
