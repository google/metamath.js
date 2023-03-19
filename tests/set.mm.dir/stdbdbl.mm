include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cle.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "crab.mm"
include "cbl.mm"
include "cif.mm"
include "wceq.mm"
include "simpll2.mm"
include "simpr1.mm"
include "adantr.mm"
include "simpr.mm"
include "stdbdmetval.mm"
include "syl3anc.mm"
include "breq1d.mm"
include "wn.mm"
include "simplr3.mm"
include "biantrud.mm"
include "wb.mm"
include "simpr2.mm"
include "simpl1.mm"
include "xmetcl.mm"
include "xrlemin.mm"
include "bitr4d.mm"
include "notbid.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "ifcld.mm"
include "3bitr4d.mm"
include "rabbidva.mm"
include "stdbdxmet.mm"
include "blval.mm"
include "3eqtr4d.mm"

theorem stdbdbl
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cX: class X
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cJ: class J
  let cB: class B
  assume stdbdmet.1: |- D = ( x e. X , y e. X |-> if ( ( x C y ) <_ R , ( x C y ) , R ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint P x
  disjoint P y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J z
  disjoint S z
  disjoint B x
  disjoint B y
  disjoint P z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X r
  disjoint X s
  disjoint X z
  assert |- ( ( ( C e. ( *Met ` X ) /\ R e. RR* /\ 0 < R ) /\ ( P e. X /\ S e. RR* /\ S <_ R ) ) -> ( P ( ball ` D ) S ) = ( P ( ball ` C ) S ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cR
    cxr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    w3a
    #
    cP
    cX
    wcel
    #
    cS
    cxr
    wcel
    #
    cS
    cR
    cle
    wbr
    #
    w3a
    #
    wa
    #
    cP
    vz
    cv
    #
    cD
    co
    #
    cS
    clt
    wbr
    #
    vz
    cX
    crab
    #
    cP
    @10
    cC
    co
    #
    cS
    clt
    wbr
    #
    vz
    cX
    crab
    #
    cP
    cS
    cD
    cbl
    cfv
    co
    #
    cP
    cS
    cC
    cbl
    cfv
    co
    #
    @9
    @12
    @15
    vz
    cX
    @9
    @10
    cX
    wcel
    #
    wa
    #
    @12
    @14
    cR
    cle
    wbr
    #
    @14
    cR
    cif
    #
    cS
    clt
    wbr
    #
    @15
    @20
    @11
    @22
    cS
    clt
    @20
    @2
    @5
    @19
    @11
    @22
    wceq
    @1
    @2
    @3
    @8
    @19
    simpll2
    #
    @9
    @5
    @19
    @4
    @5
    @6
    @7
    simpr1
    #
    adantr
    #
    @9
    @19
    simpr
    #
    vx
    vy
    cP
    @10
    cC
    cD
    cR
    cxr
    cX
    stdbdmet.1
    stdbdmetval
    syl3anc
    breq1d
    @20
    cS
    @14
    cle
    wbr
    #
    wn
    #
    cS
    @22
    cle
    wbr
    #
    wn
    #
    @15
    @23
    @20
    @28
    @30
    @20
    @28
    @28
    @7
    wa
    #
    @30
    @20
    @7
    @28
    @5
    @6
    @7
    @4
    @19
    simplr3
    biantrud
    @20
    @6
    @14
    cxr
    wcel
    #
    @2
    @30
    @32
    wb
    @9
    @6
    @19
    @4
    @5
    @6
    @7
    simpr2
    #
    adantr
    #
    @20
    @1
    @5
    @19
    @33
    @9
    @1
    @19
    @1
    @2
    @3
    @8
    simpl1
    #
    adantr
    @26
    @27
    cP
    @10
    cC
    cX
    xmetcl
    syl3anc
    #
    @24
    cS
    @14
    cR
    xrlemin
    syl3anc
    bitr4d
    notbid
    @20
    @33
    @6
    @15
    @29
    wb
    @37
    @35
    @14
    cS
    xrltnle
    syl2anc
    @20
    @22
    cxr
    wcel
    @6
    @23
    @31
    wb
    @20
    @21
    @14
    cR
    cxr
    @37
    @24
    ifcld
    @35
    @22
    cS
    xrltnle
    syl2anc
    3bitr4d
    bitr4d
    rabbidva
    @9
    cD
    @0
    wcel
    #
    @5
    @6
    @17
    @13
    wceq
    @4
    @38
    @8
    vx
    vy
    cC
    cD
    cR
    cX
    stdbdmet.1
    stdbdxmet
    adantr
    @25
    @34
    vz
    cD
    cP
    cS
    cX
    blval
    syl3anc
    @9
    @1
    @5
    @6
    @18
    @16
    wceq
    @36
    @25
    @34
    vz
    cC
    cP
    cS
    cX
    blval
    syl3anc
    3eqtr4d
end
