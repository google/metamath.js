include "cr.mm"
include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "clog.mm"
include "cfv.mm"
include "csu.mm"
include "ccht.mm"
include "df-cht.mm"
include "wcel.mm"
include "ppifi.mm"
include "wa.mm"
include "cn.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "fsumrecl.mm"
include "fmpti.mm"

theorem chtf
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- theta : RR --> RR

  proof
    vx
    cr
    cr
    cc0
    vx
    cv
    #
    cicc
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    ccht
    vx
    vp
    df-cht
    @0
    cr
    wcel
    #
    @2
    @4
    vp
    @0
    ppifi
    @5
    @3
    @2
    wcel
    #
    wa
    #
    @3
    @7
    @3
    @7
    @3
    cprime
    wcel
    @3
    cn
    wcel
    @7
    @2
    cprime
    @3
    @1
    cprime
    inss2
    @5
    @6
    simpr
    sseldi
    @3
    prmnn
    syl
    nnrpd
    relogcld
    fsumrecl
    fmpti
end
