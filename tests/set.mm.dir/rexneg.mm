include "cr.mm"
include "wcel.mm"
include "cxne.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "cneg.mm"
include "cif.mm"
include "df-xneg.mm"
include "wne.mm"
include "renepnf.mm"
include "ifnefalse.mm"
include "syl.mm"
include "renemnf.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem rexneg
  let cA: class A


  assert |- ( A e. RR -> -e A = -u A )

  proof
    cA
    cr
    wcel
    #
    cA
    cxne
    cA
    cpnf
    wceq
    cmnf
    cA
    cmnf
    wceq
    cpnf
    cA
    cneg
    #
    cif
    #
    cif
    #
    @1
    cA
    df-xneg
    @0
    @3
    @2
    @1
    @0
    cA
    cpnf
    wne
    @3
    @2
    wceq
    cA
    renepnf
    cA
    cpnf
    cmnf
    @2
    ifnefalse
    syl
    @0
    cA
    cmnf
    wne
    @2
    @1
    wceq
    cA
    renemnf
    cA
    cmnf
    cpnf
    @1
    ifnefalse
    syl
    eqtrd
    syl5eq
end
