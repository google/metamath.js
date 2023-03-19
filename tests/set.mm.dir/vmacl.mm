include "cn.mm"
include "wcel.mm"
include "cvma.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "eleq1.mm"
include "wne.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cprime.mm"
include "isppw2.mm"
include "wa.mm"
include "clog.mm"
include "vmappw.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "syl6bi.mm"
include "imp.mm"
include "0red.mm"
include "pm2.61ne.mm"

theorem vmacl
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


  assert |- ( A e. NN -> ( Lam ` A ) e. RR )

  proof
    cA
    cn
    wcel
    #
    cA
    cvma
    cfv
    #
    cr
    wcel
    #
    cc0
    cr
    wcel
    @1
    cc0
    @1
    cc0
    cr
    eleq1
    @0
    @1
    cc0
    wne
    #
    @2
    @0
    @3
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
    @2
    cA
    vk
    vp
    isppw2
    @7
    @2
    vp
    vk
    cprime
    cn
    @4
    cprime
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    @2
    @7
    @6
    cvma
    cfv
    #
    cr
    wcel
    @10
    @11
    @4
    clog
    cfv
    #
    cr
    @4
    @5
    vmappw
    @8
    @12
    cr
    wcel
    @9
    @8
    @4
    @8
    @4
    @4
    prmnn
    nnrpd
    relogcld
    adantr
    eqeltrd
    @7
    @1
    @11
    cr
    cA
    @6
    cvma
    fveq2
    eleq1d
    syl5ibrcom
    rexlimivv
    syl6bi
    imp
    @0
    0red
    pm2.61ne
end
