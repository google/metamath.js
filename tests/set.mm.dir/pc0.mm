include "cprime.mm"
include "wcel.mm"
include "cc0.mm"
include "cq.mm"
include "cpc.mm"
include "co.mm"
include "cpnf.mm"
include "wceq.mm"
include "cz.mm"
include "0z.mm"
include "zq.mm"
include "ax-mp.mm"
include "cv.mm"
include "cdiv.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmin.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "cio.mm"
include "cif.mm"
include "iftrue.mm"
include "adantl.mm"
include "df-pc.mm"
include "pnfex.mm"
include "ovmpt2a.mm"
include "mpan2.mm"

theorem pc0
  let cP: class P
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z
  let cN: class N


  assert |- ( P e. Prime -> ( P pCnt 0 ) = +oo )

  proof
    cP
    cprime
    wcel
    cc0
    cq
    wcel
    #
    cP
    cc0
    cpc
    co
    cpnf
    wceq
    cc0
    cz
    wcel
    @0
    0z
    cc0
    zq
    ax-mp
    vp
    vr
    cP
    cc0
    cprime
    cq
    vr
    cv
    #
    cc0
    wceq
    #
    cpnf
    @1
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    wceq
    vz
    cv
    vp
    cv
    #
    vn
    cv
    cexp
    co
    #
    @3
    cdvds
    wbr
    vn
    cn0
    crab
    cr
    clt
    csup
    @6
    @4
    cdvds
    wbr
    vn
    cn0
    crab
    cr
    clt
    csup
    cmin
    co
    wceq
    wa
    vy
    cn
    wrex
    vx
    cz
    wrex
    vz
    cio
    #
    cif
    #
    cpnf
    cpc
    @2
    @8
    cpnf
    wceq
    @5
    cP
    wceq
    @2
    cpnf
    @7
    iftrue
    adantl
    vx
    vy
    vz
    vn
    vr
    vp
    df-pc
    pnfex
    ovmpt2a
    mpan2
end
