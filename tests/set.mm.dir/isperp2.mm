include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cs3.mm"
include "crag.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "eqidd.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "crn.mm"
include "simp-4r.mm"
include "perpneq.mm"
include "simpllr.mm"
include "tglineineq.mm"
include "s3eqd.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "imp.mm"
include "wrex.mm"
include "isperp.mm"
include "biimpa.mm"
include "r19.29a.mm"
include "wceq.mm"
include "id.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "sylan.mm"
include "wb.mm"
include "adantr.mm"
include "mpbird.mm"
include "impbida.mm"

theorem isperp2
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume isperp2.b: |- ( ph -> B e. ran L )
  assume isperp2.x: |- ( ph -> X e. ( A i^i B ) )

  disjoint u v
  disjoint X u
  disjoint X v
  disjoint u v
  disjoint A u
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint G u
  disjoint G v
  disjoint ph u
  disjoint ph v
  disjoint u x
  disjoint v x
  disjoint X x
  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint A b
  disjoint u x
  disjoint v x
  disjoint A x
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint a g
  disjoint G a
  disjoint b g
  disjoint G b
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint G g
  disjoint G x
  disjoint L a
  disjoint L b
  disjoint L g
  disjoint a ph
  disjoint b ph
  disjoint g ph
  disjoint ph x
  assert |- ( ph -> ( A ( perpG ` G ) B <-> A. u e. A A. v e. B <" u X v "> e. ( raG ` G ) ) )

  proof
    wph
    cA
    cB
    cG
    cperpg
    cfv
    wbr
    #
    vu
    cv
    #
    cX
    vv
    cv
    #
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    #
    vv
    cB
    wral
    #
    vu
    cA
    wral
    #
    wph
    @0
    wa
    #
    @1
    vx
    cv
    #
    @2
    cs3
    #
    @4
    wcel
    #
    vv
    cB
    wral
    #
    vu
    cA
    wral
    #
    @7
    vx
    cA
    cB
    cin
    #
    @8
    @9
    @14
    wcel
    #
    wa
    #
    @13
    @7
    @16
    @12
    @6
    vu
    cA
    @16
    @1
    cA
    wcel
    #
    wa
    #
    @11
    @5
    vv
    cB
    @18
    @2
    cB
    wcel
    #
    wa
    #
    @11
    @5
    @20
    @10
    @3
    @4
    @20
    @1
    @9
    @2
    @2
    @1
    cX
    @20
    @1
    eqidd
    @20
    cA
    cB
    cP
    cG
    cI
    cL
    @9
    cX
    isperp.p
    isperp.i
    isperp.l
    wph
    cG
    cstrkg
    wcel
    @0
    @15
    @17
    @19
    isperp.g
    ad4antr
    #
    wph
    cA
    cL
    crn
    #
    wcel
    @0
    @15
    @17
    @19
    isperp.a
    ad4antr
    #
    wph
    cB
    @22
    wcel
    @0
    @15
    @17
    @19
    isperp2.b
    ad4antr
    #
    @20
    cA
    cB
    cP
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @21
    @23
    @24
    wph
    @0
    @15
    @17
    @19
    simp-4r
    perpneq
    @8
    @15
    @17
    @19
    simpllr
    wph
    cX
    @14
    wcel
    #
    @0
    @15
    @17
    @19
    isperp2.x
    ad4antr
    tglineineq
    @20
    @2
    eqidd
    s3eqd
    eleq1d
    biimpd
    ralimdva
    ralimdva
    imp
    wph
    @0
    @13
    vx
    @14
    wrex
    #
    wph
    vx
    vv
    vu
    cA
    cB
    cP
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    isperp2.b
    isperp
    #
    biimpa
    r19.29a
    wph
    @7
    wa
    @0
    @26
    wph
    @25
    @7
    @26
    isperp2.x
    @13
    @7
    vx
    cX
    @14
    @9
    cX
    wceq
    #
    @11
    @5
    vu
    vv
    cA
    cB
    @28
    @10
    @3
    @4
    @28
    @1
    @9
    @2
    @2
    @1
    cX
    @28
    @1
    eqidd
    @28
    id
    @28
    @2
    eqidd
    s3eqd
    eleq1d
    2ralbidv
    rspcev
    sylan
    wph
    @0
    @26
    wb
    @7
    @27
    adantr
    mpbird
    impbida
end
