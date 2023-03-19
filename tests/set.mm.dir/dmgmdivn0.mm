include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "cc0.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "eldifad.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "dividd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "addcld.mm"
include "wcel.mm"
include "cn0.mm"
include "wne.mm"
include "nnnn0d.mm"
include "dmgmaddn0.mm"
include "syl2anc.mm"
include "divne0d.mm"
include "eqnetrrd.mm"

theorem dmgmdivn0
  let wph: wff ph
  let cA: class A
  let cM: class M
  assume dmgmn0.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )
  assume dmgmdivn0.a: |- ( ph -> M e. NN )


  assert |- ( ph -> ( ( A / M ) + 1 ) =/= 0 )

  proof
    wph
    cA
    cM
    caddc
    co
    #
    cM
    cdiv
    co
    #
    cA
    cM
    cdiv
    co
    #
    c1
    caddc
    co
    #
    cc0
    wph
    @1
    @2
    cM
    cM
    cdiv
    co
    #
    caddc
    co
    @3
    wph
    cA
    cM
    cM
    wph
    cA
    cc
    cz
    cn
    cdif
    #
    dmgmn0.a
    eldifad
    #
    wph
    cM
    dmgmdivn0.a
    nncnd
    #
    @7
    wph
    cM
    dmgmdivn0.a
    nnne0d
    #
    divdird
    wph
    @4
    c1
    @2
    caddc
    wph
    cM
    @7
    @8
    dividd
    oveq2d
    eqtrd
    wph
    @0
    cM
    wph
    cA
    cM
    @6
    @7
    addcld
    @7
    wph
    cA
    cc
    @5
    cdif
    wcel
    cM
    cn0
    wcel
    @0
    cc0
    wne
    dmgmn0.a
    wph
    cM
    dmgmdivn0.a
    nnnn0d
    cA
    cM
    dmgmaddn0
    syl2anc
    @8
    divne0d
    eqnetrrd
end
