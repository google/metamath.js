include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "metdsf.mm"
include "iccssxr.mm"
include "fss.mm"
include "sylancl.mm"
include "simprr.mm"
include "cle.mm"
include "cxne.mm"
include "cxad.mm"
include "cif.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "xrsdsval.mm"
include "syl2anc.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplrr.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "metdscnlem.mm"
include "breq1.mm"
include "ifboth.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "ralrimivva.mm"
include "wb.mm"
include "simpl.mm"
include "xrsxmet.mm"
include "metcn.mm"
include "mpbir2and.mm"

theorem metdscn
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vs: setvar s
  let vt: setvar t
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cR: class R
  let cT: class T
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )
  assume metdscn.c: |- C = ( dist ` RR*s )
  assume metdscn.k: |- K = ( MetOpen ` C )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint J y
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
  assert |- ( ( D e. ( *Met ` X ) /\ S C_ X ) -> F e. ( J Cn K ) )

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
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cxr
    cF
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    cD
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    cC
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cX
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    vz
    cX
    wral
    #
    @2
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    @19
    cxr
    wss
    @4
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    cc0
    cpnf
    iccssxr
    cX
    @19
    cxr
    cF
    fss
    sylancl
    #
    @2
    @17
    vz
    vr
    cX
    crp
    @2
    @5
    cX
    wcel
    #
    @13
    crp
    wcel
    #
    wa
    #
    wa
    #
    @22
    @7
    @13
    clt
    wbr
    #
    @14
    wi
    #
    vw
    cX
    wral
    #
    @17
    @2
    @21
    @22
    simprr
    @24
    @26
    vw
    cX
    @24
    @6
    cX
    wcel
    #
    @25
    @14
    @24
    @28
    @25
    wa
    #
    wa
    #
    @12
    @10
    @11
    cle
    wbr
    #
    @11
    @10
    cxne
    cxad
    co
    #
    @10
    @11
    cxne
    cxad
    co
    #
    cif
    #
    @13
    clt
    @30
    @10
    cxr
    wcel
    @11
    cxr
    wcel
    @12
    @34
    wceq
    @30
    cX
    cxr
    @5
    cF
    @2
    @4
    @23
    @29
    @20
    ad2antrr
    #
    @2
    @21
    @22
    @29
    simplrl
    #
    ffvelrnd
    @30
    cX
    cxr
    @6
    cF
    @35
    @24
    @28
    @25
    simprl
    #
    ffvelrnd
    @10
    @11
    cC
    metdscn.c
    xrsdsval
    syl2anc
    @30
    @32
    @13
    clt
    wbr
    #
    @33
    @13
    clt
    wbr
    #
    @34
    @13
    clt
    wbr
    #
    @30
    vx
    vy
    @6
    @5
    cC
    cD
    @13
    cS
    cF
    cJ
    cK
    cX
    metdscn.f
    metdscn.j
    metdscn.c
    metdscn.k
    @0
    @1
    @23
    @29
    simplll
    #
    @0
    @1
    @23
    @29
    simpllr
    #
    @37
    @36
    @2
    @21
    @22
    @29
    simplrr
    #
    @30
    @6
    @5
    cD
    co
    #
    @7
    @13
    clt
    @30
    @0
    @28
    @21
    @44
    @7
    wceq
    @41
    @37
    @36
    @6
    @5
    cD
    cX
    xmetsym
    syl3anc
    @24
    @28
    @25
    simprr
    #
    eqbrtrd
    metdscnlem
    @30
    vx
    vy
    @5
    @6
    cC
    cD
    @13
    cS
    cF
    cJ
    cK
    cX
    metdscn.f
    metdscn.j
    metdscn.c
    metdscn.k
    @41
    @42
    @36
    @37
    @43
    @45
    metdscnlem
    @31
    @38
    @39
    @40
    @32
    @33
    @32
    @34
    @13
    clt
    breq1
    @33
    @34
    @13
    clt
    breq1
    ifboth
    syl2anc
    eqbrtrd
    expr
    ralrimiva
    @16
    @27
    vs
    @13
    crp
    @8
    @13
    wceq
    #
    @15
    @26
    vw
    cX
    @46
    @9
    @25
    @14
    @8
    @13
    @7
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    @2
    @0
    cC
    cxr
    cxmt
    cfv
    wcel
    @3
    @4
    @18
    wa
    wb
    @0
    @1
    simpl
    cC
    metdscn.c
    xrsxmet
    vz
    vr
    vs
    vw
    cD
    cC
    cF
    cJ
    cK
    cX
    cxr
    metdscn.j
    metdscn.k
    metcn
    sylancl
    mpbir2and
end
