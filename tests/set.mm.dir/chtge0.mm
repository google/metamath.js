include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "csu.mm"
include "ccht.mm"
include "cle.mm"
include "ppifi.mm"
include "wa.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmuz2.mm"
include "syl.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nnred.mm"
include "simprd.mm"
include "rplogcld.mm"
include "rpge0d.mm"
include "fsumge0.mm"
include "chtval.mm"
include "breqtrrd.mm"

theorem chtge0
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. RR -> 0 <_ ( theta ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cc0
    cA
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
    cA
    ccht
    cfv
    cle
    @0
    @2
    @4
    vp
    cA
    ppifi
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @3
    @6
    @3
    @6
    @3
    cn
    wcel
    #
    c1
    @3
    clt
    wbr
    #
    @6
    @3
    c2
    cuz
    cfv
    wcel
    #
    @7
    @8
    wa
    @6
    @3
    cprime
    wcel
    @9
    @6
    @2
    cprime
    @3
    @1
    cprime
    inss2
    @0
    @5
    simpr
    sseldi
    @3
    prmuz2
    syl
    @3
    eluz2b2
    sylib
    #
    simpld
    #
    nnrpd
    relogcld
    @6
    @4
    @6
    @3
    @6
    @3
    @11
    nnred
    @6
    @7
    @8
    @10
    simprd
    rplogcld
    rpge0d
    fsumge0
    cA
    vp
    chtval
    breqtrrd
end
