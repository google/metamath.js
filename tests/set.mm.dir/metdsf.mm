include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "wf.mm"
include "simplll.mm"
include "simplr.mm"
include "sselda.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "infxrcl.mm"
include "wral.mm"
include "xmetge0.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "0xr.mm"
include "infxrgelb.mm"
include "sylancl.mm"
include "mpbird.mm"
include "elxrge0.mm"
include "sylanbrc.mm"

theorem metdsf
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
  assert |- ( ( D e. ( *Met ` X ) /\ S C_ X ) -> F : X --> ( 0 [,] +oo ) )

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
    vx
    cX
    vy
    cS
    vx
    cv
    #
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
    cc0
    cpnf
    cicc
    co
    #
    cF
    @2
    @3
    cX
    wcel
    #
    wa
    #
    @8
    cxr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    @8
    @9
    wcel
    @11
    @7
    cxr
    wss
    #
    @12
    @11
    cS
    cxr
    @6
    wf
    @14
    @11
    vy
    cS
    @5
    cxr
    @6
    @11
    @4
    cS
    wcel
    #
    wa
    #
    @0
    @10
    @4
    cX
    wcel
    #
    @5
    cxr
    wcel
    @0
    @1
    @10
    @15
    simplll
    #
    @2
    @10
    @15
    simplr
    #
    @11
    cS
    cX
    @4
    @0
    @1
    @10
    simplr
    sselda
    #
    @3
    @4
    cD
    cX
    xmetcl
    syl3anc
    @6
    eqid
    #
    fmptd
    cS
    cxr
    @6
    frn
    syl
    #
    @7
    infxrcl
    syl
    @11
    @13
    cc0
    vz
    cv
    #
    cle
    wbr
    #
    vz
    @7
    wral
    #
    @11
    cc0
    @5
    cle
    wbr
    #
    vy
    cS
    wral
    #
    @25
    @11
    @26
    vy
    cS
    @16
    @0
    @10
    @17
    @26
    @18
    @19
    @20
    @3
    @4
    cD
    cX
    xmetge0
    syl3anc
    ralrimiva
    @5
    cvv
    wcel
    #
    vy
    cS
    wral
    @25
    @27
    wb
    @28
    vy
    cS
    @3
    @4
    cD
    ovex
    rgenw
    @24
    @26
    vy
    vz
    cS
    @5
    @6
    cvv
    @21
    @23
    @5
    cc0
    cle
    breq2
    ralrnmpt
    ax-mp
    sylibr
    @11
    @14
    cc0
    cxr
    wcel
    @13
    @25
    wb
    @22
    0xr
    vz
    @7
    cc0
    infxrgelb
    sylancl
    mpbird
    @8
    elxrge0
    sylanbrc
    metdscn.f
    fmptd
end
