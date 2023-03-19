include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "caddc.mm"
include "cconcat.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "ccatfval.mm"
include "3adant3.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "iftrue.mm"
include "3ad2ant3.mm"
include "sylan9eqr.mm"
include "cn0.mm"
include "simp3.mm"
include "lencl.mm"
include "3ad2ant2.mm"
include "elfzoext.mm"
include "syl2anc.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem ccatval1
  let cB: class B
  let cS: class S
  let cT: class T
  let cI: class I
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B /\ I e. ( 0 ..^ ( # ` S ) ) ) -> ( ( S ++ T ) ` I ) = ( S ` I ) )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cI
    cc0
    cS
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    vx
    cI
    vx
    cv
    #
    @4
    wcel
    #
    @7
    cS
    cfv
    #
    @7
    @3
    cmin
    co
    #
    cT
    cfv
    #
    cif
    #
    cI
    cS
    cfv
    #
    cc0
    @3
    cT
    chash
    cfv
    #
    caddc
    co
    cfzo
    co
    #
    cS
    cT
    cconcat
    co
    #
    cvv
    @1
    @2
    @16
    vx
    @15
    @12
    cmpt
    wceq
    @5
    vx
    cS
    cT
    @0
    @0
    ccatfval
    3adant3
    @7
    cI
    wceq
    #
    @6
    @12
    @5
    @13
    cI
    @3
    cmin
    co
    #
    cT
    cfv
    #
    cif
    #
    @13
    @17
    @8
    @5
    @9
    @11
    @13
    @19
    @7
    cI
    @4
    eleq1
    @7
    cI
    cS
    fveq2
    @17
    @10
    @18
    cT
    @7
    cI
    @3
    cmin
    oveq1
    fveq2d
    ifbieq12d
    @5
    @1
    @20
    @13
    wceq
    @2
    @5
    @13
    @19
    iftrue
    3ad2ant3
    sylan9eqr
    @6
    @5
    @14
    cn0
    wcel
    #
    cI
    @15
    wcel
    @1
    @2
    @5
    simp3
    @2
    @1
    @21
    @5
    cB
    cT
    lencl
    3ad2ant2
    @14
    cc0
    @3
    cI
    elfzoext
    syl2anc
    @6
    cI
    cS
    fvexd
    fvmptd
end
