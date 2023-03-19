include "cbcc.mm"
include "co.mm"
include "cfallfac.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cc.mm"
include "bccval.mm"
include "wcel.mm"
include "cn0.mm"
include "fallfaccl.mm"
include "syl2anc.mm"
include "cn.mm"
include "faccl.mm"
include "syl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "eqeltrd.mm"

theorem bcccl
  let wph: wff ph
  let cC: class C
  let cK: class K
  let vc: setvar c
  let vk: setvar k
  assume bccval.c: |- ( ph -> C e. CC )
  assume bccval.k: |- ( ph -> K e. NN0 )


  assert |- ( ph -> ( C _Cc K ) e. CC )

  proof
    wph
    cC
    cK
    cbcc
    co
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
    cc
    wph
    cC
    cK
    bccval.c
    bccval.k
    bccval
    wph
    @0
    @1
    wph
    cC
    cc
    wcel
    cK
    cn0
    wcel
    #
    @0
    cc
    wcel
    bccval.c
    bccval.k
    cC
    cK
    fallfaccl
    syl2anc
    wph
    @1
    wph
    @2
    @1
    cn
    wcel
    bccval.k
    cK
    faccl
    syl
    #
    nncnd
    wph
    @1
    @3
    nnne0d
    divcld
    eqeltrd
end
