include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wn.mm"
include "prmuz2.mm"
include "eqid.mm"
include "pcprendvds.mm"
include "sylan.mm"
include "pczpre.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "mtbird.mm"

theorem pczndvds
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ ( N e. ZZ /\ N =/= 0 ) ) -> -. ( P ^ ( ( P pCnt N ) + 1 ) ) || N )

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
    c1
    caddc
    co
    #
    cexp
    co
    #
    cN
    cdvds
    wbr
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
    c1
    caddc
    co
    #
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @1
    @10
    wn
    cP
    prmuz2
    @6
    cP
    @7
    vn
    cN
    @6
    eqid
    @7
    eqid
    #
    pcprendvds
    sylan
    @2
    @5
    @9
    cN
    cdvds
    @2
    @4
    @8
    cP
    cexp
    @2
    @3
    @7
    c1
    caddc
    cP
    @7
    vn
    cN
    @11
    pczpre
    oveq1d
    oveq2d
    breq1d
    mtbird
end
