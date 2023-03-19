include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cbcc.mm"
include "cfallfac.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "fallfacp1.mm"
include "syl2anc.mm"
include "facp1.mm"
include "syl.mm"
include "oveq12d.mm"
include "peano2nn0.mm"
include "bccval.mm"
include "fallfaccl.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "nnne0d.mm"
include "nn0p1nn.mm"
include "divmuldivd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"

theorem bccp1k
  let wph: wff ph
  let cC: class C
  let cK: class K
  let vc: setvar c
  let vk: setvar k
  assume bccval.c: |- ( ph -> C e. CC )
  assume bccval.k: |- ( ph -> K e. NN0 )


  assert |- ( ph -> ( C _Cc ( K + 1 ) ) = ( ( C _Cc K ) x. ( ( C - K ) / ( K + 1 ) ) ) )

  proof
    wph
    cC
    cK
    c1
    caddc
    co
    #
    cbcc
    co
    #
    cC
    cK
    cfallfac
    co
    #
    cK
    cfa
    cfv
    #
    cdiv
    co
    #
    cC
    cK
    cmin
    co
    #
    @0
    cdiv
    co
    #
    cmul
    co
    #
    cC
    cK
    cbcc
    co
    #
    @6
    cmul
    co
    wph
    cC
    @0
    cfallfac
    co
    #
    @0
    cfa
    cfv
    #
    cdiv
    co
    @2
    @5
    cmul
    co
    #
    @3
    @0
    cmul
    co
    #
    cdiv
    co
    @1
    @7
    wph
    @9
    @11
    @10
    @12
    cdiv
    wph
    cC
    cc
    wcel
    #
    cK
    cn0
    wcel
    #
    @9
    @11
    wceq
    bccval.c
    bccval.k
    cC
    cK
    fallfacp1
    syl2anc
    wph
    @14
    @10
    @12
    wceq
    bccval.k
    cK
    facp1
    syl
    oveq12d
    wph
    cC
    @0
    bccval.c
    wph
    @14
    @0
    cn0
    wcel
    bccval.k
    cK
    peano2nn0
    syl
    #
    bccval
    wph
    @2
    @3
    @5
    @0
    wph
    @13
    @14
    @2
    cc
    wcel
    bccval.c
    bccval.k
    cC
    cK
    fallfaccl
    syl2anc
    wph
    @3
    wph
    @14
    @3
    cn
    wcel
    bccval.k
    cK
    faccl
    syl
    #
    nncnd
    wph
    cC
    cK
    bccval.c
    wph
    cK
    bccval.k
    nn0cnd
    subcld
    wph
    @0
    @15
    nn0cnd
    wph
    @3
    @16
    nnne0d
    wph
    @0
    wph
    @14
    @0
    cn
    wcel
    bccval.k
    cK
    nn0p1nn
    syl
    nnne0d
    divmuldivd
    3eqtr4d
    wph
    @8
    @4
    @6
    cmul
    wph
    cC
    cK
    bccval.c
    bccval.k
    bccval
    oveq1d
    eqtr4d
end
