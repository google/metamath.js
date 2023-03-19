include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "gausslemma2dlem0b.mm"
include "nnzd.mm"
include "gausslemma2dlem0d.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "gausslemma2dlem0g.mm"
include "nnred.mm"
include "nn0red.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"

theorem gausslemma2dlem0h
  let wph: wff ph
  let cP: class P
  let cH: class H
  let cM: class M
  let cN: class N
  assume gausslemma2dlem0.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2dlem0.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2dlem0.n: |- N = ( H - M )


  assert |- ( ph -> N e. NN0 )

  proof
    wph
    cN
    cH
    cM
    cmin
    co
    #
    cn0
    gausslemma2dlem0.n
    wph
    @0
    cz
    wcel
    cc0
    @0
    cle
    wbr
    #
    @0
    cn0
    wcel
    wph
    cH
    cM
    wph
    cH
    wph
    cP
    cH
    gausslemma2dlem0.p
    gausslemma2dlem0.h
    gausslemma2dlem0b
    #
    nnzd
    wph
    cM
    wph
    cP
    cM
    gausslemma2dlem0.p
    gausslemma2dlem0.m
    gausslemma2dlem0d
    #
    nn0zd
    zsubcld
    wph
    @1
    cM
    cH
    cle
    wbr
    wph
    cP
    cH
    cM
    gausslemma2dlem0.p
    gausslemma2dlem0.m
    gausslemma2dlem0.h
    gausslemma2dlem0g
    wph
    cH
    cM
    wph
    cH
    @2
    nnred
    wph
    cM
    @3
    nn0red
    subge0d
    mpbird
    @0
    elnn0z
    sylanbrc
    syl5eqel
end
