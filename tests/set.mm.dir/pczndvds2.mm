include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
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
include "pcprendvds2.mm"
include "sylan.mm"
include "pczpre.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "mtbird.mm"

theorem pczndvds2
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ ( N e. ZZ /\ N =/= 0 ) ) -> -. P || ( N / ( P ^ ( P pCnt N ) ) ) )

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
    cN
    cP
    cP
    cN
    cpc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    cP
    cN
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
    cdiv
    co
    #
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
    pcprendvds2
    sylan
    @2
    @5
    @9
    cP
    cdvds
    @2
    @4
    @8
    cN
    cdiv
    @2
    @3
    @7
    cP
    cexp
    cP
    @7
    vn
    cN
    @11
    pczpre
    oveq2d
    oveq2d
    breq2d
    mtbird
end
