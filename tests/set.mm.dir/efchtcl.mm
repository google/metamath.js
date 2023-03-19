include "cr.mm"
include "wcel.mm"
include "ccht.mm"
include "cfv.mm"
include "ce.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "cn.mm"
include "chtval.mm"
include "fveq2d.mm"
include "ppifi.mm"
include "wa.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "reeflogd.mm"
include "eqeltrd.mm"
include "efnnfsumcl.mm"

theorem efchtcl
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


  assert |- ( A e. RR -> ( exp ` ( theta ` A ) ) e. NN )

  proof
    cA
    cr
    wcel
    #
    cA
    ccht
    cfv
    #
    ce
    cfv
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
    #
    ce
    cfv
    cn
    @0
    @1
    @6
    ce
    cA
    vp
    chtval
    fveq2d
    @0
    @3
    @5
    vp
    cA
    ppifi
    @0
    @4
    @3
    wcel
    #
    wa
    #
    @4
    @8
    @4
    @8
    @4
    cprime
    wcel
    @4
    cn
    wcel
    @8
    @3
    cprime
    @4
    @2
    cprime
    inss2
    @0
    @7
    simpr
    sseldi
    @4
    prmnn
    syl
    #
    nnrpd
    #
    relogcld
    @8
    @5
    ce
    cfv
    @4
    cn
    @8
    @4
    @10
    reeflogd
    @9
    eqeltrd
    efnnfsumcl
    eqeltrd
end
