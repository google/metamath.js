include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cdvn.mm"
include "cfv.mm"
include "cc0.mm"
include "caddc.mm"
include "cdv.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "dvnp1.mm"
include "mp3an3.mm"
include "dvn0.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5eqr.mm"

theorem dvn1
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let cN: class N
  let vs: setvar s


  assert |- ( ( S C_ CC /\ F e. ( CC ^pm S ) ) -> ( ( S Dn F ) ` 1 ) = ( S _D F ) )

  proof
    cS
    cc
    wss
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    wa
    #
    c1
    cS
    cF
    cdvn
    co
    #
    cfv
    cc0
    c1
    caddc
    co
    #
    @3
    cfv
    #
    cS
    cF
    cdv
    co
    #
    @4
    c1
    @3
    0p1e1
    fveq2i
    @2
    @5
    cS
    cc0
    @3
    cfv
    #
    cdv
    co
    #
    @6
    @0
    @1
    cc0
    cn0
    wcel
    @5
    @8
    wceq
    0nn0
    cS
    cF
    cc0
    dvnp1
    mp3an3
    @2
    @7
    cF
    cS
    cdv
    cS
    cF
    dvn0
    oveq2d
    eqtrd
    syl5eqr
end
