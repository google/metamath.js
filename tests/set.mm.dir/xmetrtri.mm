include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cxne.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "3ancomb.mm"
include "xmettri.mm"
include "sylan2b.mm"
include "cxr.mm"
include "cc0.mm"
include "cmnf.mm"
include "wne.mm"
include "wb.mm"
include "xmetcl.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "3adant3r3.mm"
include "xmetge0.mm"
include "ge0nemnf.mm"
include "syl2anc.mm"
include "xlesubadd.mm"
include "syl33anc.mm"
include "mpbird.mm"

theorem xmetrtri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R


  assert |- ( ( D e. ( *Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D C ) +e -e ( B D C ) ) <_ ( A D B ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cC
    cD
    co
    #
    cB
    cC
    cD
    co
    #
    cxne
    cxad
    co
    cA
    cB
    cD
    co
    #
    cle
    wbr
    #
    @6
    @8
    @7
    cxad
    co
    cle
    wbr
    #
    @4
    @0
    @1
    @3
    @2
    w3a
    @10
    @1
    @2
    @3
    3ancomb
    cA
    cC
    cB
    cD
    cX
    xmettri
    sylan2b
    @5
    @6
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    @8
    cxr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @7
    cmnf
    wne
    #
    cc0
    @8
    cle
    wbr
    #
    @9
    @10
    wb
    @0
    @1
    @3
    @11
    @2
    cA
    cC
    cD
    cX
    xmetcl
    3adant3r2
    @0
    @2
    @3
    @12
    @1
    cB
    cC
    cD
    cX
    xmetcl
    3adant3r1
    #
    @0
    @1
    @2
    @13
    @3
    cA
    cB
    cD
    cX
    xmetcl
    3adant3r3
    @0
    @1
    @3
    @14
    @2
    cA
    cC
    cD
    cX
    xmetge0
    3adant3r2
    @5
    @12
    cc0
    @7
    cle
    wbr
    #
    @15
    @17
    @0
    @2
    @3
    @18
    @1
    cB
    cC
    cD
    cX
    xmetge0
    3adant3r1
    @7
    ge0nemnf
    syl2anc
    @0
    @1
    @2
    @16
    @3
    cA
    cB
    cD
    cX
    xmetge0
    3adant3r3
    @6
    @7
    @8
    xlesubadd
    syl33anc
    mpbird
end
