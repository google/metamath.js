include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "clcm.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "lcmval.mm"
include "iffalse.mm"
include "sylan9eq.mm"

theorem lcmn0val
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cK: class K

  disjoint M n
  disjoint N n
  disjoint K n
  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 \/ N = 0 ) ) -> ( M lcm N ) = inf ( { n e. NN | ( M || n /\ N || n ) } , RR , < ) )

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
    wo
    #
    wn
    cM
    cN
    clcm
    co
    @0
    cc0
    cM
    vn
    cv
    #
    cdvds
    wbr
    cN
    @1
    cdvds
    wbr
    wa
    vn
    cn
    crab
    cr
    clt
    cinf
    #
    cif
    @2
    vn
    cM
    cN
    lcmval
    @0
    cc0
    @2
    iffalse
    sylan9eq
end
