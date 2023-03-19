include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wa.mm"
include "ssrab2.mm"
include "dvdsdivcl.mm"
include "sylan.mm"
include "sseldi.mm"
include "fsumdvdsdiaglem.mm"
include "impbid.mm"
include "fsumcom2.mm"

theorem fsumdvdsdiag
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  assume fsumdvdsdiag.1: |- ( ph -> N e. NN )
  assume fsumdvdsdiag.2: |- ( ( ph /\ ( j e. { x e. NN | x || N } /\ k e. { x e. NN | x || ( N / j ) } ) ) -> A e. CC )

  disjoint j k
  disjoint j x
  disjoint N j
  disjoint k x
  disjoint N k
  disjoint N x
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> sum_ j e. { x e. NN | x || N } sum_ k e. { x e. NN | x || ( N / j ) } A = sum_ k e. { x e. NN | x || N } sum_ j e. { x e. NN | x || ( N / k ) } A )

  proof
    wph
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @0
    cN
    vj
    cv
    #
    cdiv
    co
    #
    cdvds
    wbr
    vx
    cn
    crab
    #
    @2
    @0
    cN
    vk
    cv
    #
    cdiv
    co
    cdvds
    wbr
    vx
    cn
    crab
    #
    vj
    vk
    cA
    wph
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    @2
    @8
    wss
    #
    @2
    cfn
    wcel
    wph
    c1
    cN
    fzfid
    wph
    cN
    cn
    wcel
    #
    @9
    fsumdvdsdiag.1
    cN
    vx
    dvdsssfz1
    syl
    @8
    @2
    ssfi
    syl2anc
    #
    @11
    wph
    @3
    @2
    wcel
    #
    wa
    #
    c1
    @4
    cfz
    co
    #
    cfn
    wcel
    @5
    @14
    wss
    #
    @5
    cfn
    wcel
    @13
    c1
    @4
    fzfid
    @13
    @4
    cn
    wcel
    @15
    @13
    @2
    cn
    @4
    @1
    vx
    cn
    ssrab2
    wph
    @10
    @12
    @4
    @2
    wcel
    fsumdvdsdiag.1
    vx
    @3
    cN
    dvdsdivcl
    sylan
    sseldi
    @4
    vx
    dvdsssfz1
    syl
    @14
    @5
    ssfi
    syl2anc
    wph
    @12
    @6
    @5
    wcel
    wa
    @6
    @2
    wcel
    @3
    @7
    wcel
    wa
    wph
    vx
    vj
    vk
    cN
    fsumdvdsdiag.1
    fsumdvdsdiaglem
    wph
    vx
    vk
    vj
    cN
    fsumdvdsdiag.1
    fsumdvdsdiaglem
    impbid
    fsumdvdsdiag.2
    fsumcom2
end
