include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cfn.mm"
include "etransclem12.mm"
include "wcel.mm"
include "wss.mm"
include "fzfi.mm"
include "mapfi.mm"
include "mp2an.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "syl6eqel.mm"

theorem etransclem16
  let wph: wff ph
  let cC: class C
  let vj: setvar j
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume etransclem16.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem16.n: |- ( ph -> N e. NN0 )

  disjoint M c
  disjoint M n
  disjoint c n
  disjoint N c
  disjoint N n
  disjoint j n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( C ` N ) e. Fin )

  proof
    wph
    cN
    cC
    cfv
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
    cfn
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem16.c
    etransclem16.n
    etransclem12
    @3
    cfn
    wcel
    #
    @4
    @3
    wss
    @4
    cfn
    wcel
    @2
    cfn
    wcel
    @0
    cfn
    wcel
    @5
    cc0
    cN
    fzfi
    cc0
    cM
    fzfi
    @2
    @0
    mapfi
    mp2an
    @1
    vc
    @3
    ssrab2
    @3
    @4
    ssfi
    mp2an
    syl6eqel
end
