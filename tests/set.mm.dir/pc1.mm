include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cpc.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cc0.mm"
include "cz.mm"
include "wne.mm"
include "wceq.mm"
include "1z.mm"
include "ax-1ne0.mm"
include "eqid.mm"
include "pczpre.mm"
include "mpanr12.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "pcpre1.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem pc1
  let cP: class P
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z
  let cN: class N


  assert |- ( P e. Prime -> ( P pCnt 1 ) = 0 )

  proof
    cP
    cprime
    wcel
    #
    cP
    c1
    cpc
    co
    #
    cP
    vn
    cv
    cexp
    co
    c1
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
    cc0
    @0
    c1
    cz
    wcel
    c1
    cc0
    wne
    @1
    @3
    wceq
    1z
    ax-1ne0
    cP
    @3
    vn
    c1
    @3
    eqid
    #
    pczpre
    mpanr12
    @0
    cP
    c2
    cuz
    cfv
    wcel
    c1
    c1
    wceq
    @3
    cc0
    wceq
    cP
    prmuz2
    c1
    eqid
    @2
    cP
    @3
    vn
    c1
    @2
    eqid
    @4
    pcpre1
    sylancl
    eqtrd
end
