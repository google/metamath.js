include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "clp.mm"
include "w3a.mm"
include "crp.mm"
include "wa.mm"
include "cbl.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "cnei.mm"
include "wral.mm"
include "simpl1.mm"
include "cuni.mm"
include "ctop.mm"
include "mopntop.mm"
include "syl.mm"
include "simpl2.mm"
include "wceq.mm"
include "mopnuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "lpss.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "sseldd.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "blnei.mm"
include "syl3anc.mm"
include "wb.mm"
include "islp2.mm"
include "mpbid.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "rspcva.mm"
include "wex.mm"
include "elin.mm"
include "eldifi.mm"
include "anim2i.mm"
include "ancomd.mm"
include "sylbi.mm"
include "eximi.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4i.mm"

theorem lpbl
  let vx: setvar x
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let cA: class A
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )

  disjoint D x
  disjoint J x
  disjoint R x
  disjoint S x
  disjoint P x
  disjoint X x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J r
  disjoint J y
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S y
  disjoint N r
  disjoint N y
  disjoint P r
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint T z
  disjoint X r
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( ( D e. ( *Met ` X ) /\ S C_ X /\ P e. ( ( limPt ` J ) ` S ) ) /\ R e. RR+ ) -> E. x e. S x e. ( P ( ball ` D ) R ) )

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
    cP
    cS
    cJ
    clp
    cfv
    cfv
    #
    wcel
    #
    w3a
    #
    cR
    crp
    wcel
    #
    wa
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cS
    cP
    csn
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    vx
    cv
    #
    @7
    wcel
    #
    vx
    cS
    wrex
    #
    @6
    @7
    @8
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    @12
    @9
    cin
    #
    c0
    wne
    #
    vx
    @15
    wral
    #
    @11
    @6
    @0
    cP
    cX
    wcel
    @5
    @16
    @0
    @1
    @3
    @5
    simpl1
    #
    @6
    cP
    cJ
    cuni
    #
    cX
    @6
    @2
    @21
    cP
    @6
    cJ
    ctop
    wcel
    #
    cS
    @21
    wss
    #
    @2
    @21
    wss
    @6
    @0
    @22
    @20
    cD
    cJ
    cX
    mopni.1
    mopntop
    syl
    #
    @6
    cS
    cX
    @21
    @0
    @1
    @3
    @5
    simpl2
    @6
    @0
    cX
    @21
    wceq
    @20
    cD
    cJ
    cX
    mopni.1
    mopnuni
    syl
    #
    sseqtrd
    #
    cS
    cJ
    @21
    @21
    eqid
    #
    lpss
    syl2anc
    @0
    @1
    @3
    @5
    simpl3
    #
    sseldd
    #
    @25
    eleqtrrd
    @4
    @5
    simpr
    cD
    cP
    cR
    cJ
    cX
    mopni.1
    blnei
    syl3anc
    @6
    @3
    @19
    @28
    @6
    @22
    @23
    cP
    @21
    wcel
    @3
    @19
    wb
    @24
    @26
    @29
    cP
    cS
    vx
    cJ
    @21
    @27
    islp2
    syl3anc
    mpbid
    @18
    @11
    vx
    @7
    @15
    @12
    @7
    wceq
    @17
    @10
    c0
    @12
    @7
    @9
    ineq1
    neeq1d
    rspcva
    syl2anc
    @12
    @10
    wcel
    #
    vx
    wex
    @12
    cS
    wcel
    #
    @13
    wa
    #
    vx
    wex
    @11
    @14
    @30
    @32
    vx
    @30
    @13
    @12
    @9
    wcel
    #
    wa
    #
    @32
    @12
    @7
    @9
    elin
    @34
    @13
    @31
    @33
    @31
    @13
    @12
    cS
    @8
    eldifi
    anim2i
    ancomd
    sylbi
    eximi
    vx
    @10
    n0
    @13
    vx
    cS
    df-rex
    3imtr4i
    syl
end
