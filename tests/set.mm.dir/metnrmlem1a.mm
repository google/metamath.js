include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cle.mm"
include "cif.mm"
include "crp.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wn.mm"
include "adantr.mm"
include "wne.mm"
include "wi.mm"
include "inelcm.mm"
include "expcom.mm"
include "adantl.mm"
include "necon2bd.mm"
include "mpd.mm"
include "ccl.mm"
include "eqcom.mm"
include "cxmt.mm"
include "wss.mm"
include "wb.mm"
include "cuni.mm"
include "ccld.mm"
include "eqid.mm"
include "cldss.mm"
include "syl.mm"
include "mopnuni.mm"
include "sseqtr4d.mm"
include "simpr.mm"
include "sseldd.mm"
include "metdseq0.mm"
include "syl3anc.mm"
include "syl5bb.mm"
include "cldcls.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "mtbird.mm"
include "wo.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "metdsf.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "cxr.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "0xr.mm"
include "simplbi.mm"
include "xrleloe.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ord.mm"
include "mt3d.mm"
include "cr.mm"
include "1re.mm"
include "rexri.mm"
include "ifcl.mm"
include "1red.mm"
include "0lt1.mm"
include "breq2.mm"
include "ifboth.mm"
include "xrltle.mm"
include "xrmin1.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "elrpd.mm"
include "jca.mm"

theorem metnrmlem1a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
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
  let cB: class B
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
  assert |- ( ( ph /\ A e. T ) -> ( 0 < ( F ` A ) /\ if ( 1 <_ ( F ` A ) , 1 , ( F ` A ) ) e. RR+ ) )

  proof
    wph
    cA
    cT
    wcel
    #
    wa
    #
    cc0
    cA
    cF
    cfv
    #
    clt
    wbr
    #
    c1
    @2
    cle
    wbr
    #
    c1
    @2
    cif
    #
    crp
    wcel
    @1
    @3
    cc0
    @2
    wceq
    #
    @1
    @6
    cA
    cS
    wcel
    #
    @1
    cS
    cT
    cin
    #
    c0
    wceq
    #
    @7
    wn
    wph
    @9
    @0
    metnrmlem.4
    adantr
    @1
    @7
    @8
    c0
    @0
    @7
    @8
    c0
    wne
    #
    wi
    wph
    @7
    @0
    @10
    cA
    cS
    cT
    inelcm
    expcom
    adantl
    necon2bd
    mpd
    @1
    @6
    cA
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @7
    @6
    @2
    cc0
    wceq
    #
    @1
    @12
    cc0
    @2
    eqcom
    @1
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
    @13
    @12
    wb
    wph
    @14
    @0
    metnrmlem.1
    adantr
    #
    @1
    cS
    cJ
    cuni
    #
    cX
    @1
    cS
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    @17
    wss
    wph
    @19
    @0
    metnrmlem.2
    adantr
    #
    cS
    cJ
    @17
    @17
    eqid
    #
    cldss
    syl
    @1
    @14
    cX
    @17
    wceq
    @16
    cD
    cJ
    cX
    metdscn.j
    mopnuni
    syl
    #
    sseqtr4d
    #
    @1
    cT
    cX
    cA
    @1
    cT
    @17
    cX
    @1
    cT
    @18
    wcel
    #
    cT
    @17
    wss
    wph
    @24
    @0
    metnrmlem.3
    adantr
    cT
    cJ
    @17
    @21
    cldss
    syl
    @22
    sseqtr4d
    wph
    @0
    simpr
    sseldd
    #
    vx
    vy
    cA
    cD
    cS
    cF
    cJ
    cX
    metdscn.f
    metdscn.j
    metdseq0
    syl3anc
    syl5bb
    @1
    @11
    cS
    cA
    @1
    @19
    @11
    cS
    wceq
    @20
    cS
    cJ
    cldcls
    syl
    eleq2d
    bitrd
    mtbird
    @1
    @3
    @6
    @1
    cc0
    @2
    cle
    wbr
    #
    @3
    @6
    wo
    #
    @1
    @2
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @26
    @1
    cX
    @28
    cA
    cF
    @1
    @14
    @15
    cX
    @28
    cF
    wf
    @16
    @23
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    syl2anc
    @25
    ffvelrnd
    #
    @29
    @2
    cxr
    wcel
    #
    @26
    @2
    elxrge0
    #
    simprbi
    syl
    @1
    cc0
    cxr
    wcel
    #
    @31
    @26
    @27
    wb
    0xr
    @1
    @29
    @31
    @30
    @29
    @31
    @26
    @32
    simplbi
    syl
    #
    cc0
    @2
    xrleloe
    sylancr
    mpbid
    ord
    mt3d
    #
    @1
    @5
    @1
    @5
    cxr
    wcel
    #
    c1
    cr
    wcel
    cc0
    @5
    cle
    wbr
    #
    @5
    c1
    cle
    wbr
    #
    @5
    cr
    wcel
    @1
    c1
    cxr
    wcel
    #
    @31
    @36
    c1
    1re
    rexri
    #
    @34
    @4
    c1
    @2
    cxr
    ifcl
    sylancr
    #
    @1
    1red
    @1
    cc0
    @5
    clt
    wbr
    #
    @37
    @1
    cc0
    c1
    clt
    wbr
    #
    @3
    @42
    0lt1
    @35
    @4
    @43
    @3
    @42
    c1
    @2
    c1
    @5
    cc0
    clt
    breq2
    @2
    @5
    cc0
    clt
    breq2
    ifboth
    sylancr
    #
    @1
    @33
    @36
    @42
    @37
    wi
    0xr
    @41
    cc0
    @5
    xrltle
    sylancr
    mpd
    @1
    @39
    @31
    @38
    @40
    @34
    c1
    @2
    xrmin1
    sylancr
    @5
    c1
    xrrege0
    syl22anc
    @44
    elrpd
    jca
end
