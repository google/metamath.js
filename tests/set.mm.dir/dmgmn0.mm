include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "eldifad.mm"
include "addid1d.mm"
include "wcel.mm"
include "cn0.mm"
include "wne.mm"
include "0nn0.mm"
include "dmgmaddn0.mm"
include "sylancl.mm"
include "eqnetrrd.mm"

theorem dmgmn0
  let wph: wff ph
  let cA: class A
  assume dmgmn0.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )


  assert |- ( ph -> A =/= 0 )

  proof
    wph
    cA
    cc0
    caddc
    co
    #
    cA
    cc0
    wph
    cA
    wph
    cA
    cc
    cz
    cn
    cdif
    #
    dmgmn0.a
    eldifad
    addid1d
    wph
    cA
    cc
    @1
    cdif
    wcel
    cc0
    cn0
    wcel
    @0
    cc0
    wne
    dmgmn0.a
    0nn0
    cA
    cc0
    dmgmaddn0
    sylancl
    eqnetrrd
end
