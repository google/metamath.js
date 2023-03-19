include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c4.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "oveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "nnoddn2prm.mm"
include "nnz.mm"
include "anim1i.mm"
include "3syl.mm"
include "flodddiv4t2lthalf.mm"
include "syl.mm"
include "syl5eqbr.mm"

theorem gausslemma2dlem0e
  let wph: wff ph
  let cP: class P
  let cM: class M
  assume gausslemma2dlem0.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0.m: |- M = ( |_ ` ( P / 4 ) )


  assert |- ( ph -> ( M x. 2 ) < ( P / 2 ) )

  proof
    wph
    cM
    c2
    cmul
    co
    cP
    c4
    cdiv
    co
    cfl
    cfv
    #
    c2
    cmul
    co
    #
    cP
    c2
    cdiv
    co
    #
    clt
    cM
    @0
    c2
    cmul
    gausslemma2dlem0.m
    oveq1i
    wph
    cP
    cz
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
    @1
    @2
    clt
    wbr
    wph
    cP
    cprime
    c2
    csn
    cdif
    wcel
    cP
    cn
    wcel
    #
    @4
    wa
    @5
    gausslemma2dlem0.p
    cP
    nnoddn2prm
    @6
    @3
    @4
    cP
    nnz
    anim1i
    3syl
    cP
    flodddiv4t2lthalf
    syl
    syl5eqbr
end
