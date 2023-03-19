include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cn.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "caddc.mm"
include "cn0.mm"
include "wa.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "prmuz2.mm"
include "syl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "nnoddn2prm.mm"
include "nnoddm1d2.mm"
include "biimpa.mm"
include "nnnn0d.mm"
include "jca.mm"
include "nno.mm"
include "syl5eqel.mm"

theorem gausslemma2dlem0b
  let wph: wff ph
  let cP: class P
  let cH: class H
  assume gausslemma2dlem0a.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0b.h: |- H = ( ( P - 1 ) / 2 )


  assert |- ( ph -> H e. NN )

  proof
    wph
    cH
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cn
    gausslemma2dlem0b.h
    wph
    cP
    c2
    cuz
    cfv
    wcel
    #
    cP
    c1
    caddc
    co
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    wa
    #
    @0
    cn
    wcel
    wph
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @4
    gausslemma2dlem0a.p
    @6
    @1
    @3
    @6
    cP
    cprime
    wcel
    @1
    cP
    cprime
    @5
    eldifi
    cP
    prmuz2
    syl
    @6
    cP
    cn
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    @3
    cP
    nnoddn2prm
    @9
    @2
    @7
    @8
    @2
    cn
    wcel
    cP
    nnoddm1d2
    biimpa
    nnnn0d
    syl
    jca
    syl
    cP
    nno
    syl
    syl5eqel
end
