include "caddc.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cn0.mm"
include "wn.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "eldifad.mm"
include "nn0cnd.mm"
include "addcld.mm"
include "wa.mm"
include "eldmgm.mm"
include "sylib.mm"
include "simprd.mm"
include "wceq.mm"
include "cmin.mm"
include "negdi2d.mm"
include "oveq1d.mm"
include "negcld.mm"
include "npcand.mm"
include "eqtrd.mm"
include "adantr.mm"
include "simpr.mm"
include "nn0addcld.mm"
include "eqeltrrd.mm"
include "mtand.mm"
include "sylanbrc.mm"

theorem dmgmaddnn0
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume dmgmn0.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )
  assume dmgmaddnn0.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A + N ) e. ( CC \ ( ZZ \ NN ) ) )

  proof
    wph
    cA
    cN
    caddc
    co
    #
    cc
    wcel
    @0
    cneg
    #
    cn0
    wcel
    #
    wn
    @0
    cc
    cz
    cn
    cdif
    #
    cdif
    #
    wcel
    wph
    cA
    cN
    wph
    cA
    cc
    @3
    dmgmn0.a
    eldifad
    #
    wph
    cN
    dmgmaddnn0.n
    nn0cnd
    #
    addcld
    wph
    @2
    cA
    cneg
    #
    cn0
    wcel
    #
    wph
    cA
    cc
    wcel
    #
    @8
    wn
    #
    wph
    cA
    @4
    wcel
    @9
    @10
    wa
    dmgmn0.a
    cA
    eldmgm
    sylib
    simprd
    wph
    @2
    wa
    #
    @1
    cN
    caddc
    co
    #
    @7
    cn0
    wph
    @12
    @7
    wceq
    @2
    wph
    @12
    @7
    cN
    cmin
    co
    #
    cN
    caddc
    co
    @7
    wph
    @1
    @13
    cN
    caddc
    wph
    cA
    cN
    @5
    @6
    negdi2d
    oveq1d
    wph
    @7
    cN
    wph
    cA
    @5
    negcld
    @6
    npcand
    eqtrd
    adantr
    @11
    @1
    cN
    wph
    @2
    simpr
    wph
    cN
    cn0
    wcel
    @2
    dmgmaddnn0.n
    adantr
    nn0addcld
    eqeltrrd
    mtand
    @0
    eldmgm
    sylanbrc
end
