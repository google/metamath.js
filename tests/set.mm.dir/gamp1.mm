include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clgam.mm"
include "cfv.mm"
include "ce.mm"
include "cmul.mm"
include "cgam.mm"
include "clog.mm"
include "lgamp1.mm"
include "fveq2d.mm"
include "wceq.mm"
include "lgamcl.mm"
include "eldifi.mm"
include "id.mm"
include "dmgmn0.mm"
include "logcld.mm"
include "efadd.mm"
include "syl2anc.mm"
include "cc0.mm"
include "wne.mm"
include "eflog.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cn0.mm"
include "1nn0.mm"
include "a1i.mm"
include "dmgmaddnn0.mm"
include "eflgam.mm"
include "syl.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"

theorem gamp1
  let cA: class A
  let vm: setvar m


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( _G ` ( A + 1 ) ) = ( ( _G ` A ) x. A ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    #
    cdif
    #
    wcel
    #
    cA
    c1
    caddc
    co
    #
    clgam
    cfv
    #
    ce
    cfv
    #
    cA
    clgam
    cfv
    #
    ce
    cfv
    #
    cA
    cmul
    co
    #
    @3
    cgam
    cfv
    #
    cA
    cgam
    cfv
    #
    cA
    cmul
    co
    @2
    @5
    @6
    cA
    clog
    cfv
    #
    caddc
    co
    #
    ce
    cfv
    #
    @7
    @11
    ce
    cfv
    #
    cmul
    co
    #
    @8
    @2
    @4
    @12
    ce
    cA
    lgamp1
    fveq2d
    @2
    @6
    cc
    wcel
    @11
    cc
    wcel
    @13
    @15
    wceq
    cA
    lgamcl
    @2
    cA
    cA
    cc
    @0
    eldifi
    #
    @2
    cA
    @2
    id
    #
    dmgmn0
    #
    logcld
    @6
    @11
    efadd
    syl2anc
    @2
    @14
    cA
    @7
    cmul
    @2
    cA
    cc
    wcel
    cA
    cc0
    wne
    @14
    cA
    wceq
    @16
    @18
    cA
    eflog
    syl2anc
    oveq2d
    3eqtrd
    @2
    @3
    @1
    wcel
    @5
    @9
    wceq
    @2
    cA
    c1
    @17
    c1
    cn0
    wcel
    @2
    1nn0
    a1i
    dmgmaddnn0
    @3
    eflgam
    syl
    @2
    @7
    @10
    cA
    cmul
    cA
    eflgam
    oveq1d
    3eqtr3d
end
