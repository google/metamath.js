include "cn.mm"
include "wcel.mm"
include "cvma.mm"
include "cfv.mm"
include "ce.mm"
include "c1.mm"
include "cc0.mm"
include "wceq.mm"
include "fveq2.mm"
include "ef0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "wne.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wrex.mm"
include "cprime.mm"
include "isppw2.mm"
include "wa.mm"
include "clog.mm"
include "vmappw.mm"
include "fveq2d.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "reeflogd.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "syl6bi.mm"
include "imp.mm"
include "1nn.mm"
include "a1i.mm"
include "pm2.61ne.mm"

theorem efvmacl
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


  assert |- ( A e. NN -> ( exp ` ( Lam ` A ) ) e. NN )

  proof
    cA
    cn
    wcel
    #
    cA
    cvma
    cfv
    #
    ce
    cfv
    #
    cn
    wcel
    #
    c1
    cn
    wcel
    #
    @1
    cc0
    @1
    cc0
    wceq
    #
    @2
    c1
    cn
    @5
    @2
    cc0
    ce
    cfv
    c1
    @1
    cc0
    ce
    fveq2
    ef0
    syl6eq
    eleq1d
    @0
    @1
    cc0
    wne
    #
    @3
    @0
    @6
    cA
    vp
    cv
    #
    vk
    cv
    #
    cexp
    co
    #
    wceq
    #
    vk
    cn
    wrex
    vp
    cprime
    wrex
    @3
    cA
    vk
    vp
    isppw2
    @10
    @3
    vp
    vk
    cprime
    cn
    @7
    cprime
    wcel
    #
    @8
    cn
    wcel
    #
    wa
    #
    @3
    @10
    @9
    cvma
    cfv
    #
    ce
    cfv
    #
    cn
    wcel
    @13
    @15
    @7
    clog
    cfv
    #
    ce
    cfv
    #
    cn
    @13
    @14
    @16
    ce
    @7
    @8
    vmappw
    fveq2d
    @11
    @17
    cn
    wcel
    @12
    @11
    @17
    @7
    cn
    @11
    @7
    @11
    @7
    @7
    prmnn
    #
    nnrpd
    reeflogd
    @18
    eqeltrd
    adantr
    eqeltrd
    @10
    @2
    @15
    cn
    @10
    @1
    @14
    ce
    cA
    @9
    cvma
    fveq2
    fveq2d
    eleq1d
    syl5ibrcom
    rexlimivv
    syl6bi
    imp
    @4
    @0
    1nn
    a1i
    pm2.61ne
end
