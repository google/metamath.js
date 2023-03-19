include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wa.mm"
include "zabscl.mm"
include "3anim1i.mm"
include "adantr.mm"
include "wb.mm"
include "absdvdsb.mm"
include "3adant3.mm"
include "biimpa.mm"
include "dvdsleabs.mm"
include "sylc.mm"
include "ex.mm"

theorem dvdsleabs2
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( M || N -> ( abs ` M ) <_ ( abs ` N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    w3a
    #
    cM
    cN
    cdvds
    wbr
    #
    cM
    cabs
    cfv
    #
    cN
    cabs
    cfv
    cle
    wbr
    #
    @3
    @4
    wa
    @5
    cz
    wcel
    #
    @1
    @2
    w3a
    #
    @5
    cN
    cdvds
    wbr
    #
    @6
    @3
    @8
    @4
    @0
    @7
    @1
    @2
    cM
    zabscl
    3anim1i
    adantr
    @3
    @4
    @9
    @0
    @1
    @4
    @9
    wb
    @2
    cM
    cN
    absdvdsb
    3adant3
    biimpa
    @5
    cN
    dvdsleabs
    sylc
    ex
end
