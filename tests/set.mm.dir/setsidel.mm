include "cop.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wcel.mm"
include "opex.mm"
include "snid.mm"
include "elun2.mm"
include "mp1i.mm"
include "csts.mm"
include "co.mm"
include "wceq.mm"
include "setsval.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "eleqtrrd.mm"

theorem setsidel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume setsidel.s: |- ( ph -> S e. V )
  assume setsidel.b: |- ( ph -> B e. W )
  assume setsidel.r: |- R = ( S sSet <. A , B >. )


  assert |- ( ph -> <. A , B >. e. R )

  proof
    wph
    cA
    cB
    cop
    #
    cS
    cvv
    cA
    csn
    cdif
    cres
    #
    @0
    csn
    #
    cun
    #
    cR
    @0
    @2
    wcel
    @0
    @3
    wcel
    wph
    @0
    cA
    cB
    opex
    snid
    @0
    @2
    @1
    elun2
    mp1i
    wph
    cR
    cS
    @0
    csts
    co
    #
    @3
    setsidel.r
    wph
    cS
    cV
    wcel
    cB
    cW
    wcel
    @4
    @3
    wceq
    setsidel.s
    setsidel.b
    cA
    cB
    cS
    cV
    cW
    setsval
    syl2anc
    syl5eq
    eleqtrrd
end
