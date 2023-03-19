include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cn0.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "wcel.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem etransclem12
  let wph: wff ph
  let cC: class C
  let vj: setvar j
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume etransclem12.1: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem12.2: |- ( ph -> N e. NN0 )

  disjoint M c
  disjoint M n
  disjoint c n
  disjoint N c
  disjoint N n
  disjoint j n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( C ` N ) = { c e. ( ( 0 ... N ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = N } )

  proof
    wph
    vn
    cN
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    vc
    cv
    cfv
    vj
    csu
    #
    vn
    cv
    #
    wceq
    #
    vc
    cc0
    @2
    cfz
    co
    #
    @0
    cmap
    co
    #
    crab
    #
    @1
    cN
    wceq
    #
    vc
    cc0
    cN
    cfz
    co
    #
    @0
    cmap
    co
    #
    crab
    #
    cn0
    cC
    cvv
    cC
    vn
    cn0
    @6
    cmpt
    wceq
    wph
    etransclem12.1
    a1i
    @2
    cN
    wceq
    #
    @6
    @10
    wceq
    wph
    @11
    @3
    @7
    vc
    @5
    @9
    @11
    @4
    @8
    @0
    cmap
    @2
    cN
    cc0
    cfz
    oveq2
    oveq1d
    @2
    cN
    @1
    eqeq2
    rabeqbidv
    adantl
    etransclem12.2
    @10
    cvv
    wcel
    wph
    @7
    vc
    @9
    @8
    @0
    cmap
    ovex
    rabex
    a1i
    fvmptd
end
