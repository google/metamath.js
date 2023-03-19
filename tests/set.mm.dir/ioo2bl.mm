include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "cbl.mm"
include "cfv.mm"
include "cioo.mm"
include "wceq.mm"
include "readdcl.mm"
include "ancoms.mm"
include "rehalfcld.mm"
include "resubcl.mm"
include "bl2ioo.mm"
include "syl2anc.mm"
include "cc.mm"
include "recn.mm"
include "addcom.mm"
include "syl2anr.mm"
include "oveq1d.mm"
include "halfaddsub.mm"
include "simprd.mm"
include "simpld.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"

theorem ioo2bl
  let cA: class A
  let cB: class B
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A (,) B ) = ( ( ( A + B ) / 2 ) ( ball ` D ) ( ( B - A ) / 2 ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cB
    cA
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cB
    cA
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cD
    cbl
    cfv
    #
    co
    #
    @4
    @6
    cmin
    co
    #
    @4
    @6
    caddc
    co
    #
    cioo
    co
    #
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @6
    @7
    co
    cA
    cB
    cioo
    co
    @2
    @4
    cr
    wcel
    @6
    cr
    wcel
    @8
    @11
    wceq
    @2
    @3
    @1
    @0
    @3
    cr
    wcel
    cB
    cA
    readdcl
    ancoms
    rehalfcld
    @2
    @5
    @1
    @0
    @5
    cr
    wcel
    cB
    cA
    resubcl
    ancoms
    rehalfcld
    @4
    @6
    cD
    remet.1
    bl2ioo
    syl2anc
    @2
    @4
    @13
    @6
    @7
    @2
    @3
    @12
    c2
    cdiv
    @1
    cB
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @3
    @12
    wceq
    @0
    cB
    recn
    #
    cA
    recn
    #
    cB
    cA
    addcom
    syl2anr
    oveq1d
    oveq1d
    @2
    @9
    cA
    @10
    cB
    cioo
    @2
    @10
    cB
    wceq
    #
    @9
    cA
    wceq
    #
    @1
    @14
    @15
    @18
    @19
    wa
    @0
    @16
    @17
    cB
    cA
    halfaddsub
    syl2anr
    #
    simprd
    @2
    @18
    @19
    @20
    simpld
    oveq12d
    3eqtr3rd
end
