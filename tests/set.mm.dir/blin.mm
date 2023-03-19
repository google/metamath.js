include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cbl.mm"
include "co.mm"
include "cin.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "clt.mm"
include "wb.mm"
include "xmetcl.mm"
include "3expa.mm"
include "adantlr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "xrltmin.mm"
include "syl3anc.mm"
include "pm5.32da.mm"
include "ifcl.mm"
include "elbl.mm"
include "sylan2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "anbi12d.mm"
include "elin.mm"
include "anandi.mm"
include "3bitr4g.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem blin
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C


  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X ) /\ ( R e. RR* /\ S e. RR* ) ) -> ( ( P ( ball ` D ) R ) i^i ( P ( ball ` D ) S ) ) = ( P ( ball ` D ) if ( R <_ S , R , S ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cR
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    wa
    #
    wa
    #
    vx
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    #
    cP
    cS
    @7
    co
    #
    cin
    #
    cP
    cR
    cS
    cle
    wbr
    #
    cR
    cS
    cif
    #
    @7
    co
    #
    @6
    vx
    cv
    #
    cX
    wcel
    #
    cP
    @14
    cD
    co
    #
    @12
    clt
    wbr
    #
    wa
    #
    @15
    @16
    cR
    clt
    wbr
    #
    @16
    cS
    clt
    wbr
    #
    wa
    #
    wa
    #
    @14
    @13
    wcel
    #
    @14
    @10
    wcel
    #
    @6
    @15
    @17
    @21
    @6
    @15
    wa
    @16
    cxr
    wcel
    #
    @3
    @4
    @17
    @21
    wb
    @2
    @15
    @25
    @5
    @0
    @1
    @15
    @25
    cP
    @14
    cD
    cX
    xmetcl
    3expa
    adantlr
    @2
    @3
    @4
    @15
    simplrl
    @2
    @3
    @4
    @15
    simplrr
    @16
    cR
    cS
    xrltmin
    syl3anc
    pm5.32da
    @5
    @2
    @12
    cxr
    wcel
    #
    @23
    @18
    wb
    #
    @11
    cR
    cS
    cxr
    ifcl
    @0
    @1
    @26
    @27
    @14
    cD
    cP
    @12
    cX
    elbl
    3expa
    sylan2
    @6
    @14
    @8
    wcel
    #
    @14
    @9
    wcel
    #
    wa
    @15
    @19
    wa
    #
    @15
    @20
    wa
    #
    wa
    @24
    @22
    @6
    @28
    @30
    @29
    @31
    @2
    @3
    @28
    @30
    wb
    #
    @4
    @0
    @1
    @3
    @32
    @14
    cD
    cP
    cR
    cX
    elbl
    3expa
    adantrr
    @2
    @4
    @29
    @31
    wb
    #
    @3
    @0
    @1
    @4
    @33
    @14
    cD
    cP
    cS
    cX
    elbl
    3expa
    adantrl
    anbi12d
    @14
    @8
    @9
    elin
    @15
    @19
    @20
    anandi
    3bitr4g
    3bitr4rd
    eqrdv
end
