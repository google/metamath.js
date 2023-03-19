include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cn0.mm"
include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "gausslemma2dlem0a.mm"
include "nnre.mm"
include "4re.mm"
include "a1i.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "clt.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "4pos.mm"
include "pm3.2i.mm"
include "divge0.mm"
include "syl21anc.mm"
include "jca.mm"
include "flge0nn0.mm"
include "3syl.mm"
include "syl5eqel.mm"

theorem gausslemma2dlem0d
  let wph: wff ph
  let cP: class P
  let cM: class M
  assume gausslemma2dlem0.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0.m: |- M = ( |_ ` ( P / 4 ) )


  assert |- ( ph -> M e. NN0 )

  proof
    wph
    cM
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cn0
    gausslemma2dlem0.m
    wph
    cP
    cn
    wcel
    #
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    wa
    @1
    cn0
    wcel
    wph
    cP
    gausslemma2dlem0.p
    gausslemma2dlem0a
    @2
    @3
    @4
    @2
    cP
    c4
    cP
    nnre
    #
    c4
    cr
    wcel
    #
    @2
    4re
    a1i
    c4
    cc0
    wne
    @2
    4ne0
    a1i
    redivcld
    @2
    cP
    cr
    wcel
    cc0
    cP
    cle
    wbr
    @6
    cc0
    c4
    clt
    wbr
    #
    wa
    #
    @4
    @5
    @2
    cP
    cP
    nnnn0
    nn0ge0d
    @8
    @2
    @6
    @7
    4re
    4pos
    pm3.2i
    a1i
    cP
    c4
    divge0
    syl21anc
    jca
    @0
    flge0nn0
    3syl
    syl5eqel
end
