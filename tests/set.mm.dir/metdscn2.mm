include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cxrs.mm"
include "cds.mm"
include "cmopn.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "xrsdsre.mm"
include "cxr.mm"
include "cxmt.mm"
include "wceq.mm"
include "xrsxmet.mm"
include "ressxr.mm"
include "metrest.mm"
include "mp2an.mm"
include "tgioo.mm"
include "tgioo2.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "metxmet.mm"
include "metdscn.mm"
include "sylan.mm"
include "3adant3.mm"
include "wf.mm"
include "wb.mm"
include "metdsre.mm"
include "frn.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "cnrest2.mm"
include "mp3an13.mm"
include "3syl.mm"
include "mpbid.mm"
include "sseldi.mm"

theorem metdscn2
  let vx: setvar x
  let vy: setvar y
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
  let cC: class C
  let cG: class G
  let cR: class R
  let cT: class T
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )
  assume metdscn2.k: |- K = ( TopOpen ` CCfld )

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
  assert |- ( ( D e. ( Met ` X ) /\ S C_ X /\ S =/= (/) ) -> F e. ( J Cn K ) )

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
    w3a
    #
    cJ
    cxrs
    cds
    cfv
    #
    cmopn
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    #
    cF
    @7
    cJ
    cK
    cr
    crest
    co
    #
    ccn
    co
    #
    @8
    @6
    @9
    cJ
    ccn
    cioo
    crn
    ctg
    cfv
    @6
    @9
    @4
    cr
    cr
    cxp
    cres
    #
    @6
    @4
    @4
    eqid
    #
    xrsdsre
    @4
    cxr
    cxmt
    cfv
    wcel
    #
    cr
    cxr
    wss
    #
    @6
    @11
    cmopn
    cfv
    #
    wceq
    @4
    @12
    xrsxmet
    #
    ressxr
    @4
    @11
    @5
    @15
    cxr
    cr
    @11
    eqid
    @5
    eqid
    #
    @15
    eqid
    metrest
    mp2an
    tgioo
    cK
    metdscn2.k
    tgioo2
    eqtr3i
    oveq2i
    cK
    ctop
    wcel
    @10
    @8
    wss
    cK
    metdscn2.k
    cnfldtop
    cr
    cJ
    cK
    cnrest2r
    ax-mp
    eqsstri
    @3
    cF
    cJ
    @5
    ccn
    co
    wcel
    #
    cF
    @7
    wcel
    #
    @0
    @1
    @18
    @2
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    @1
    @18
    cD
    cX
    metxmet
    vx
    vy
    @4
    cD
    cS
    cF
    cJ
    @5
    cX
    metdscn.f
    metdscn.j
    @12
    @17
    metdscn
    sylan
    3adant3
    @3
    cX
    cr
    cF
    wf
    cF
    crn
    cr
    wss
    #
    @18
    @19
    wb
    #
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsre
    cX
    cr
    cF
    frn
    @5
    cxr
    ctopon
    cfv
    wcel
    #
    @20
    @14
    @21
    @13
    @22
    @16
    @4
    @5
    cxr
    @17
    mopntopon
    ax-mp
    ressxr
    cr
    cF
    cJ
    @5
    cxr
    cnrest2
    mp3an13
    3syl
    mpbid
    sseldi
end
