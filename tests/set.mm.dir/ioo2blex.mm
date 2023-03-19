include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "cbl.mm"
include "cfv.mm"
include "crn.mm"
include "ioo2bl.mm"
include "cxr.mm"
include "readdcl.mm"
include "rehalfcld.mm"
include "resubcl.mm"
include "ancoms.mm"
include "rexrd.mm"
include "cxmt.mm"
include "rexmet.mm"
include "blelrn.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem ioo2blex
  let cA: class A
  let cB: class B
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A (,) B ) e. ran ( ball ` D ) )

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
    cA
    cB
    cioo
    co
    cA
    cB
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
    @7
    crn
    #
    cA
    cB
    cD
    remet.1
    ioo2bl
    @2
    @4
    cr
    wcel
    #
    @6
    cxr
    wcel
    #
    @8
    @9
    wcel
    #
    @2
    @3
    cA
    cB
    readdcl
    rehalfcld
    @2
    @6
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
    rexrd
    cD
    cr
    cxmt
    cfv
    wcel
    @10
    @11
    @12
    cD
    remet.1
    rexmet
    cD
    @4
    @6
    cr
    blelrn
    mp3an1
    syl2anc
    eqeltrd
end
