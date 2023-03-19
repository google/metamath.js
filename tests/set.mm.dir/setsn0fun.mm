include "cstr.mm"
include "wbr.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "wi.mm"
include "structn0fun.mm"
include "wa.mm"
include "wcel.mm"
include "cvv.mm"
include "structex.mm"
include "setsfun0.mm"
include "sylanl1.mm"
include "expcom.mm"
include "syl2anc.mm"
include "com12.mm"
include "mpdan.mm"
include "mpcom.mm"

theorem setsn0fun
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cE: class E
  let cI: class I
  let cW: class W
  let cX: class X
  assume setsn0fun.s: |- ( ph -> S Struct X )
  assume setsn0fun.i: |- ( ph -> I e. U )
  assume setsn0fun.e: |- ( ph -> E e. W )


  assert |- ( ph -> Fun ( ( S sSet <. I , E >. ) \ { (/) } ) )

  proof
    cS
    cX
    cstr
    wbr
    #
    wph
    cS
    cI
    cE
    cop
    csts
    co
    c0
    csn
    #
    cdif
    wfun
    #
    setsn0fun.s
    @0
    cS
    @1
    cdif
    wfun
    #
    wph
    @2
    wi
    cS
    cX
    structn0fun
    wph
    @0
    @3
    wa
    #
    @2
    wph
    cI
    cU
    wcel
    #
    cE
    cW
    wcel
    #
    @4
    @2
    wi
    setsn0fun.i
    setsn0fun.e
    @4
    @5
    @6
    wa
    #
    @2
    @0
    cS
    cvv
    wcel
    @3
    @7
    @2
    cS
    cX
    structex
    cU
    cE
    cS
    cI
    cvv
    cW
    setsfun0
    sylanl1
    expcom
    syl2anc
    com12
    mpdan
    mpcom
end
