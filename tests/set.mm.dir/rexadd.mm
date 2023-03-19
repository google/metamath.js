include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "cxr.mm"
include "rexr.mm"
include "xaddval.mm"
include "syl2an.mm"
include "wne.mm"
include "renepnf.mm"
include "ifnefalse.mm"
include "syl.mm"
include "renemnf.mm"
include "eqtrd.mm"
include "sylan9eq.mm"

theorem rexadd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A +e B ) = ( A + B ) )

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
    cA
    cB
    cxad
    co
    #
    cA
    cpnf
    wceq
    cB
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cA
    cmnf
    wceq
    cB
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @5
    cpnf
    @3
    cmnf
    cA
    cB
    caddc
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cif
    #
    @7
    @0
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @2
    @11
    wceq
    @1
    cA
    rexr
    cB
    rexr
    cA
    cB
    xaddval
    syl2an
    @0
    @1
    @11
    @9
    @7
    @0
    @11
    @10
    @9
    @0
    cA
    cpnf
    wne
    @11
    @10
    wceq
    cA
    renepnf
    cA
    cpnf
    @4
    @10
    ifnefalse
    syl
    @0
    cA
    cmnf
    wne
    @10
    @9
    wceq
    cA
    renemnf
    cA
    cmnf
    @6
    @9
    ifnefalse
    syl
    eqtrd
    @1
    @9
    @8
    @7
    @1
    cB
    cpnf
    wne
    @9
    @8
    wceq
    cB
    renepnf
    cB
    cpnf
    cpnf
    @8
    ifnefalse
    syl
    @1
    cB
    cmnf
    wne
    @8
    @7
    wceq
    cB
    renemnf
    cB
    cmnf
    cmnf
    @7
    ifnefalse
    syl
    eqtrd
    sylan9eq
    eqtrd
end
