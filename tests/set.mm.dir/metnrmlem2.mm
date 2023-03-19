include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "c1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cbl.mm"
include "ciun.mm"
include "ctop.mm"
include "wral.mm"
include "cxmt.mm"
include "mopntop.mm"
include "syl.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "cuni.mm"
include "ccld.mm"
include "eqid.mm"
include "cldss.mm"
include "wceq.mm"
include "mopnuni.mm"
include "sseqtr4d.mm"
include "sselda.mm"
include "cc0.mm"
include "clt.mm"
include "crp.mm"
include "metnrmlem1a.mm"
include "simprd.mm"
include "rphalfcld.mm"
include "rpxrd.mm"
include "blopn.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "iunopn.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "csn.mm"
include "blcntr.mm"
include "snssd.mm"
include "ss2iun.mm"
include "iunid.mm"
include "eqcomi.mm"
include "3sstr4g.mm"
include "jca.mm"

theorem metnrmlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vs: setvar s
  let cB: class B
  let cC: class C
  let cG: class G
  let cR: class R
  let cK: class K
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )
  assume metnrmlem.1: |- ( ph -> D e. ( *Met ` X ) )
  assume metnrmlem.2: |- ( ph -> S e. ( Clsd ` J ) )
  assume metnrmlem.3: |- ( ph -> T e. ( Clsd ` J ) )
  assume metnrmlem.4: |- ( ph -> ( S i^i T ) = (/) )
  assume metnrmlem.u: |- U = U_ t e. T ( t ( ball ` D ) ( if ( 1 <_ ( F ` t ) , 1 , ( F ` t ) ) / 2 ) )

  disjoint x y
  disjoint t x
  disjoint t y
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint J t
  disjoint J y
  disjoint ph t
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint F t
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
  disjoint t z
  disjoint D w
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J w
  disjoint J z
  disjoint ph s
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
  disjoint T w
  disjoint T z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint S s
  disjoint S w
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X z
  disjoint F r
  disjoint F s
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  assert |- ( ph -> ( U e. J /\ T C_ U ) )

  proof
    wph
    cU
    cJ
    wcel
    cT
    cU
    wss
    wph
    cU
    vt
    cT
    vt
    cv
    #
    c1
    @0
    cF
    cfv
    #
    cle
    wbr
    c1
    @1
    cif
    #
    c2
    cdiv
    co
    #
    cD
    cbl
    cfv
    co
    #
    ciun
    #
    cJ
    metnrmlem.u
    wph
    cJ
    ctop
    wcel
    #
    @4
    cJ
    wcel
    #
    vt
    cT
    wral
    @5
    cJ
    wcel
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @6
    metnrmlem.1
    cD
    cJ
    cX
    metdscn.j
    mopntop
    syl
    wph
    @7
    vt
    cT
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @8
    @0
    cX
    wcel
    #
    @3
    cxr
    wcel
    @7
    wph
    @8
    @9
    metnrmlem.1
    adantr
    #
    wph
    cT
    cX
    @0
    wph
    cT
    cJ
    cuni
    #
    cX
    wph
    cT
    cJ
    ccld
    cfv
    wcel
    cT
    @13
    wss
    metnrmlem.3
    cT
    cJ
    @13
    @13
    eqid
    cldss
    syl
    wph
    @8
    cX
    @13
    wceq
    metnrmlem.1
    cD
    cJ
    cX
    metdscn.j
    mopnuni
    syl
    sseqtr4d
    sselda
    #
    @10
    @3
    @10
    @2
    @10
    cc0
    @1
    clt
    wbr
    @2
    crp
    wcel
    wph
    vx
    vy
    @0
    cD
    cS
    cT
    cF
    cJ
    cX
    metdscn.f
    metdscn.j
    metnrmlem.1
    metnrmlem.2
    metnrmlem.3
    metnrmlem.4
    metnrmlem1a
    simprd
    rphalfcld
    #
    rpxrd
    cD
    @0
    @3
    cJ
    cX
    metdscn.j
    blopn
    syl3anc
    ralrimiva
    vt
    cT
    @4
    cJ
    iunopn
    syl2anc
    syl5eqel
    wph
    vt
    cT
    @0
    csn
    #
    ciun
    #
    @5
    cT
    cU
    wph
    @16
    @4
    wss
    #
    vt
    cT
    wral
    @17
    @5
    wss
    wph
    @18
    vt
    cT
    @10
    @0
    @4
    @10
    @8
    @11
    @3
    crp
    wcel
    @0
    @4
    wcel
    @12
    @14
    @15
    cD
    @0
    @3
    cX
    blcntr
    syl3anc
    snssd
    ralrimiva
    vt
    cT
    @16
    @4
    ss2iun
    syl
    @17
    cT
    vt
    cT
    iunid
    eqcomi
    metnrmlem.u
    3sstr4g
    jca
end
