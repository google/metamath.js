include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "gcdval.mm"
include "iffalse.mm"
include "sylan9eq.mm"

theorem gcdn0val
  let vn: setvar n
  let cM: class M
  let cN: class N

  disjoint M n
  disjoint N n
  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 /\ N = 0 ) ) -> ( M gcd N ) = sup ( { n e. ZZ | ( n || M /\ n || N ) } , RR , < ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    #
    wn
    cM
    cN
    cgcd
    co
    @0
    cc0
    vn
    cv
    #
    cM
    cdvds
    wbr
    @1
    cN
    cdvds
    wbr
    wa
    vn
    cz
    crab
    cr
    clt
    csup
    #
    cif
    @2
    vn
    cM
    cN
    gcdval
    @0
    cc0
    @2
    iffalse
    sylan9eq
end
