include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "c2.mm"
include "cle.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "c3.mm"
include "wceq.mm"
include "c5.mm"
include "cuz.mm"
include "wo.mm"
include "wbr.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "w3o.mm"
include "wi.mm"
include "prm23ge5.mm"
include "eqneqall.mm"
include "orc.mm"
include "a1d.mm"
include "olc.mm"
include "3jaoi.mm"
include "syl.mm"
include "imp.mm"
include "sylbi.mm"
include "fldiv4p1lem1div2.mm"
include "3syl.mm"
include "oveq1i.mm"
include "3brtr4g.mm"

theorem gausslemma2dlem0f
  let wph: wff ph
  let cP: class P
  let cH: class H
  let cM: class M
  assume gausslemma2dlem0.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2dlem0.h: |- H = ( ( P - 1 ) / 2 )


  assert |- ( ph -> ( M + 1 ) <_ H )

  proof
    wph
    cP
    c4
    cdiv
    co
    cfl
    cfv
    #
    c1
    caddc
    co
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
    c1
    caddc
    co
    cH
    cle
    wph
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    cP
    c3
    wceq
    #
    cP
    c5
    cuz
    cfv
    wcel
    #
    wo
    #
    @1
    @2
    cle
    wbr
    gausslemma2dlem0.p
    @3
    cP
    cprime
    wcel
    #
    cP
    c2
    wne
    #
    wa
    @6
    cP
    cprime
    c2
    eldifsn
    @7
    @8
    @6
    @7
    cP
    c2
    wceq
    #
    @4
    @5
    w3o
    @8
    @6
    wi
    #
    cP
    prm23ge5
    @9
    @10
    @4
    @5
    @6
    cP
    c2
    eqneqall
    @4
    @6
    @8
    @4
    @5
    orc
    a1d
    @5
    @6
    @8
    @5
    @4
    olc
    a1d
    3jaoi
    syl
    imp
    sylbi
    cP
    fldiv4p1lem1div2
    3syl
    cM
    @0
    c1
    caddc
    gausslemma2dlem0.m
    oveq1i
    gausslemma2dlem0.h
    3brtr4g
end
