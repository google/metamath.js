include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "eluzelcn.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an3.mm"
include "syl2anr.mm"
include "adantr.mm"
include "peano2uz.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "exp31.mm"
include "a2d.mm"
include "addid1d.mm"
include "eleq1d.mm"
include "ibir.mm"
include "oveq2.mm"
include "imbi2d.mm"
include "nn0indALT.mm"
include "impcom.mm"

theorem uzaddcl
  let cK: class K
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( N e. ( ZZ>= ` M ) /\ K e. NN0 ) -> ( N + K ) e. ( ZZ>= ` M ) )

  proof
    cK
    cn0
    wcel
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cK
    caddc
    co
    #
    @0
    wcel
    #
    @1
    cN
    vj
    cv
    #
    caddc
    co
    #
    @0
    wcel
    #
    wi
    @1
    cN
    cc0
    caddc
    co
    #
    @0
    wcel
    #
    wi
    @1
    cN
    vk
    cv
    #
    caddc
    co
    #
    @0
    wcel
    #
    wi
    @1
    cN
    @9
    c1
    caddc
    co
    #
    caddc
    co
    #
    @0
    wcel
    #
    wi
    @1
    @3
    wi
    vj
    vk
    cK
    @9
    cn0
    wcel
    #
    @1
    @11
    @14
    @15
    @1
    @11
    @14
    @15
    @1
    wa
    #
    @11
    wa
    @10
    c1
    caddc
    co
    #
    @13
    @0
    @16
    @17
    @13
    wceq
    #
    @11
    @1
    cN
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @18
    @15
    cM
    cN
    eluzelcn
    #
    @9
    nn0cn
    @19
    @20
    c1
    cc
    wcel
    @18
    ax-1cn
    cN
    @9
    c1
    addass
    mp3an3
    syl2anr
    adantr
    @11
    @17
    @0
    wcel
    @16
    cM
    @10
    peano2uz
    adantl
    eqeltrrd
    exp31
    a2d
    @1
    @8
    @1
    @7
    cN
    @0
    @1
    cN
    @21
    addid1d
    eleq1d
    ibir
    @4
    cc0
    wceq
    #
    @6
    @8
    @1
    @22
    @5
    @7
    @0
    @4
    cc0
    cN
    caddc
    oveq2
    eleq1d
    imbi2d
    @4
    @9
    wceq
    #
    @6
    @11
    @1
    @23
    @5
    @10
    @0
    @4
    @9
    cN
    caddc
    oveq2
    eleq1d
    imbi2d
    @4
    @12
    wceq
    #
    @6
    @14
    @1
    @24
    @5
    @13
    @0
    @4
    @12
    cN
    caddc
    oveq2
    eleq1d
    imbi2d
    @4
    cK
    wceq
    #
    @6
    @3
    @1
    @25
    @5
    @2
    @0
    @4
    cK
    cN
    caddc
    oveq2
    eleq1d
    imbi2d
    nn0indALT
    impcom
end
