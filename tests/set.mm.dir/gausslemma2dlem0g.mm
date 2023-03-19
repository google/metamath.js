include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "c2.mm"
include "cle.mm"
include "cn.mm"
include "wcel.mm"
include "wbr.mm"
include "gausslemma2dlem0a.mm"
include "fldiv4lem1div2.mm"
include "syl.mm"
include "3brtr4g.mm"

theorem gausslemma2dlem0g
  let wph: wff ph
  let cP: class P
  let cH: class H
  let cM: class M
  assume gausslemma2dlem0.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2dlem0.h: |- H = ( ( P - 1 ) / 2 )


  assert |- ( ph -> M <_ H )

  proof
    wph
    cP
    c4
    cdiv
    co
    cfl
    cfv
    #
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cM
    cH
    cle
    wph
    cP
    cn
    wcel
    @0
    @1
    cle
    wbr
    wph
    cP
    gausslemma2dlem0.p
    gausslemma2dlem0a
    cP
    fldiv4lem1div2
    syl
    gausslemma2dlem0.m
    gausslemma2dlem0.h
    3brtr4g
end
