include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "pczpre.mm"
include "oveq2d.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "pcprecl.mm"
include "simprd.mm"
include "sylan.mm"
include "eqbrtrd.mm"

theorem pczdvds
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ ( N e. ZZ /\ N =/= 0 ) ) -> ( P ^ ( P pCnt N ) ) || N )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    cN
    cc0
    wne
    wa
    #
    wa
    #
    cP
    cP
    cN
    cpc
    co
    #
    cexp
    co
    cP
    cP
    vn
    cv
    cexp
    co
    cN
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cexp
    co
    #
    cN
    cdvds
    @2
    @3
    @5
    cP
    cexp
    cP
    @5
    vn
    cN
    @5
    eqid
    #
    pczpre
    oveq2d
    @0
    cP
    c2
    cuz
    cfv
    wcel
    #
    @1
    @6
    cN
    cdvds
    wbr
    #
    cP
    prmuz2
    @8
    @1
    wa
    @5
    cn0
    wcel
    @9
    @4
    cP
    @5
    vn
    cN
    @4
    eqid
    @7
    pcprecl
    simprd
    sylan
    eqbrtrd
end
