include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cbc.mm"
include "cmin.mm"
include "cfallfac.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "cn0.mm"
include "cz.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2an.mm"
include "nn0cnd.mm"
include "cc.mm"
include "fznn0sub.mm"
include "fallfaccl.mm"
include "elfznn0.mm"
include "peano2nn0.mm"
include "syl.mm"
include "mulcld.mm"

theorem binomfallfaclem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vj: setvar j
  assume binomfallfaclem.1: |- ( ph -> A e. CC )
  assume binomfallfaclem.2: |- ( ph -> B e. CC )
  assume binomfallfaclem.3: |- ( ph -> N e. NN0 )


  assert |- ( ( ph /\ K e. ( 0 ... N ) ) -> ( ( N _C K ) x. ( ( A FallFac ( N - K ) ) x. ( B FallFac ( K + 1 ) ) ) ) e. CC )

  proof
    wph
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    wa
    #
    cN
    cK
    cbc
    co
    #
    cA
    cN
    cK
    cmin
    co
    #
    cfallfac
    co
    #
    cB
    cK
    c1
    caddc
    co
    #
    cfallfac
    co
    #
    cmul
    co
    @1
    @2
    wph
    cN
    cn0
    wcel
    cK
    cz
    wcel
    @2
    cn0
    wcel
    @0
    binomfallfaclem.3
    cK
    cc0
    cN
    elfzelz
    cK
    cN
    bccl
    syl2an
    nn0cnd
    @1
    @4
    @6
    wph
    cA
    cc
    wcel
    @3
    cn0
    wcel
    @4
    cc
    wcel
    @0
    binomfallfaclem.1
    cK
    cc0
    cN
    fznn0sub
    cA
    @3
    fallfaccl
    syl2an
    wph
    cB
    cc
    wcel
    @5
    cn0
    wcel
    #
    @6
    cc
    wcel
    @0
    binomfallfaclem.2
    @0
    cK
    cn0
    wcel
    @7
    cK
    cN
    elfznn0
    cK
    peano2nn0
    syl
    cB
    @5
    fallfaccl
    syl2an
    mulcld
    mulcld
end
