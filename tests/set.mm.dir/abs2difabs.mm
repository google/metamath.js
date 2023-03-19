include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "abs2dif.mm"
include "ancoms.mm"
include "wceq.mm"
include "abscl.mm"
include "recnd.mm"
include "negsubdi2.mm"
include "syl2an.mm"
include "abssub.mm"
include "3brtr4d.mm"
include "cr.mm"
include "wb.mm"
include "resubcl.mm"
include "subcl.mm"
include "syl.mm"
include "absle.mm"
include "syl2anc.mm"
include "lenegcon1.mm"
include "anbi1d.mm"
include "bitr4d.mm"
include "mpbir2and.mm"

theorem abs2difabs
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( abs ` ( ( abs ` A ) - ( abs ` B ) ) ) <_ ( abs ` ( A - B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    @5
    cneg
    #
    @7
    cle
    wbr
    #
    @5
    @7
    cle
    wbr
    #
    @2
    @4
    @3
    cmin
    co
    #
    cB
    cA
    cmin
    co
    cabs
    cfv
    #
    @9
    @7
    cle
    @1
    @0
    @12
    @13
    cle
    wbr
    cB
    cA
    abs2dif
    ancoms
    @0
    @3
    cc
    wcel
    @4
    cc
    wcel
    @9
    @12
    wceq
    @1
    @0
    @3
    cA
    abscl
    #
    recnd
    @1
    @4
    cB
    abscl
    #
    recnd
    @3
    @4
    negsubdi2
    syl2an
    cA
    cB
    abssub
    3brtr4d
    cA
    cB
    abs2dif
    @2
    @8
    @7
    cneg
    @5
    cle
    wbr
    #
    @11
    wa
    #
    @10
    @11
    wa
    @2
    @5
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @8
    @17
    wb
    @0
    @3
    cr
    wcel
    @4
    cr
    wcel
    @18
    @1
    @14
    @15
    @3
    @4
    resubcl
    syl2an
    #
    @2
    @6
    cc
    wcel
    @19
    cA
    cB
    subcl
    @6
    abscl
    syl
    #
    @5
    @7
    absle
    syl2anc
    @2
    @10
    @16
    @11
    @2
    @18
    @19
    @10
    @16
    wb
    @20
    @21
    @5
    @7
    lenegcon1
    syl2anc
    anbi1d
    bitr4d
    mpbir2and
end
