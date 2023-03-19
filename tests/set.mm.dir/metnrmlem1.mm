include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "co.mm"
include "cxr.mm"
include "1re.mm"
include "rexri.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxmt.mm"
include "wss.mm"
include "wf.mm"
include "adantr.mm"
include "cuni.mm"
include "ccld.mm"
include "eqid.mm"
include "cldss.mm"
include "syl.mm"
include "wceq.mm"
include "mopnuni.mm"
include "sseqtr4d.mm"
include "metdsf.mm"
include "syl2anc.mm"
include "simprr.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "ifcl.mm"
include "sylancr.mm"
include "simprl.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "xrmin2.mm"
include "cxad.mm"
include "metdstri.mm"
include "syl22anc.mm"
include "xmetsym.mm"
include "metds0.mm"
include "oveq12d.mm"
include "xaddid1.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "xrletrd.mm"

theorem metnrmlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let cF: class F
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  let cC: class C
  let cG: class G
  let cR: class R
  let cK: class K
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )
  assume metnrmlem.1: |- ( ph -> D e. ( *Met ` X ) )
  assume metnrmlem.2: |- ( ph -> S e. ( Clsd ` J ) )
  assume metnrmlem.3: |- ( ph -> T e. ( Clsd ` J ) )
  assume metnrmlem.4: |- ( ph -> ( S i^i T ) = (/) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint J y
  disjoint B x
  disjoint B y
  disjoint T x
  disjoint T y
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
  assert |- ( ( ph /\ ( A e. S /\ B e. T ) ) -> if ( 1 <_ ( F ` B ) , 1 , ( F ` B ) ) <_ ( A D B ) )

  proof
    wph
    cA
    cS
    wcel
    #
    cB
    cT
    wcel
    #
    wa
    #
    wa
    #
    c1
    cB
    cF
    cfv
    #
    cle
    wbr
    #
    c1
    @4
    cif
    #
    @4
    cA
    cB
    cD
    co
    #
    @3
    c1
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    @6
    cxr
    wcel
    c1
    1re
    rexri
    #
    @3
    @4
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @9
    @3
    cX
    @11
    cB
    cF
    @3
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
    cX
    @11
    cF
    wf
    wph
    @13
    @2
    metnrmlem.1
    adantr
    #
    @3
    cS
    cJ
    cuni
    #
    cX
    @3
    cS
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    @16
    wss
    wph
    @18
    @2
    metnrmlem.2
    adantr
    cS
    cJ
    @16
    @16
    eqid
    #
    cldss
    syl
    @3
    @13
    cX
    @16
    wceq
    @15
    cD
    cJ
    cX
    metdscn.j
    mopnuni
    syl
    #
    sseqtr4d
    #
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    syl2anc
    @3
    cT
    cX
    cB
    @3
    cT
    @16
    cX
    @3
    cT
    @17
    wcel
    #
    cT
    @16
    wss
    wph
    @22
    @2
    metnrmlem.3
    adantr
    cT
    cJ
    @16
    @19
    cldss
    syl
    @20
    sseqtr4d
    wph
    @0
    @1
    simprr
    sseldd
    #
    ffvelrnd
    @12
    @9
    cc0
    @4
    cle
    wbr
    @4
    elxrge0
    simplbi
    syl
    #
    @5
    c1
    @4
    cxr
    ifcl
    sylancr
    @24
    @3
    @13
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @7
    cxr
    wcel
    #
    @15
    @3
    cS
    cX
    cA
    @21
    wph
    @0
    @1
    simprl
    #
    sseldd
    #
    @23
    cA
    cB
    cD
    cX
    xmetcl
    syl3anc
    #
    @3
    @8
    @9
    @6
    @4
    cle
    wbr
    @10
    @24
    c1
    @4
    xrmin2
    sylancr
    @3
    @4
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
    @7
    cle
    @3
    @13
    @14
    @26
    @25
    @4
    @33
    cle
    wbr
    @15
    @21
    @23
    @29
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
    syl22anc
    @3
    @33
    @7
    cc0
    cxad
    co
    #
    @7
    @3
    @31
    @7
    @32
    cc0
    cxad
    @3
    @13
    @26
    @25
    @31
    @7
    wceq
    @15
    @23
    @29
    cB
    cA
    cD
    cX
    xmetsym
    syl3anc
    @3
    @13
    @14
    @0
    @32
    cc0
    wceq
    @15
    @21
    @28
    vx
    vy
    cA
    cD
    cS
    cF
    cX
    metdscn.f
    metds0
    syl3anc
    oveq12d
    @3
    @27
    @34
    @7
    wceq
    @30
    @7
    xaddid1
    syl
    eqtrd
    breqtrd
    xrletrd
end
