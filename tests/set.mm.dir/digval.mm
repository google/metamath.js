include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "cmo.mm"
include "cdig.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "digfval.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "negeq.mm"
include "oveq2d.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "adantl.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem digval
  let cB: class B
  let cR: class R
  let cK: class K
  let vb: setvar b
  let vk: setvar k
  let vr: setvar r
  let vx: setvar x


  assert |- ( ( B e. NN /\ K e. ZZ /\ R e. ( 0 [,) +oo ) ) -> ( K ( digit ` B ) R ) = ( ( |_ ` ( ( B ^ -u K ) x. R ) ) mod B ) )

  proof
    cB
    cn
    wcel
    #
    cK
    cz
    wcel
    #
    cR
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    w3a
    #
    vk
    vr
    cK
    cR
    cz
    @2
    cB
    vk
    cv
    #
    cneg
    #
    cexp
    co
    #
    vr
    cv
    #
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
    cB
    cK
    cneg
    #
    cexp
    co
    #
    cR
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
    cB
    cdig
    cfv
    #
    cvv
    @0
    @1
    @17
    vk
    vr
    cz
    @2
    @11
    cmpt2
    wceq
    @3
    cB
    vk
    vr
    digfval
    3ad2ant1
    @5
    cK
    wceq
    #
    @8
    cR
    wceq
    #
    wa
    #
    @11
    @16
    wceq
    @4
    @20
    @10
    @15
    cB
    cmo
    @20
    @9
    @14
    cfl
    @20
    @7
    @13
    @8
    cR
    cmul
    @18
    @7
    @13
    wceq
    @19
    @18
    @6
    @12
    cB
    cexp
    @5
    cK
    negeq
    oveq2d
    adantr
    @18
    @19
    simpr
    oveq12d
    fveq2d
    oveq1d
    adantl
    @0
    @1
    @3
    simp2
    @0
    @1
    @3
    simp3
    @4
    @15
    cB
    cmo
    ovexd
    ovmpt2d
end
