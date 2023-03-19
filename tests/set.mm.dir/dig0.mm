include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "cdig.mm"
include "cfv.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cmo.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "0e0icopnf.mm"
include "digval.mm"
include "mp3an3.mm"
include "cc.mm"
include "nncn.mm"
include "adantr.mm"
include "wne.mm"
include "nnne0.mm"
include "znegcl.mm"
include "adantl.mm"
include "expclzd.mm"
include "mul01d.mm"
include "fveq2d.mm"
include "0zd.mm"
include "flid.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "crp.mm"
include "nnrp.mm"
include "0mod.mm"

theorem dig0
  let cB: class B
  let cK: class K
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. NN /\ K e. ZZ ) -> ( K ( digit ` B ) 0 ) = 0 )

  proof
    cB
    cn
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cK
    cc0
    cB
    cdig
    cfv
    co
    #
    cB
    cK
    cneg
    #
    cexp
    co
    #
    cc0
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    cc0
    @0
    @1
    cc0
    cc0
    cpnf
    cico
    co
    wcel
    @3
    @8
    wceq
    0e0icopnf
    cB
    cc0
    cK
    digval
    mp3an3
    @2
    @8
    cc0
    cB
    cmo
    co
    #
    cc0
    @2
    @7
    cc0
    cB
    cmo
    @2
    @7
    cc0
    cfl
    cfv
    #
    cc0
    @2
    @6
    cc0
    cfl
    @2
    @5
    @2
    cB
    @4
    @0
    cB
    cc
    wcel
    @1
    cB
    nncn
    adantr
    @0
    cB
    cc0
    wne
    @1
    cB
    nnne0
    adantr
    @1
    @4
    cz
    wcel
    @0
    cK
    znegcl
    adantl
    expclzd
    mul01d
    fveq2d
    @2
    cc0
    cz
    wcel
    @10
    cc0
    wceq
    @2
    0zd
    cc0
    flid
    syl
    eqtrd
    oveq1d
    @0
    @9
    cc0
    wceq
    #
    @1
    @0
    cB
    crp
    wcel
    @11
    cB
    nnrp
    cB
    0mod
    syl
    adantr
    eqtrd
    eqtrd
end
