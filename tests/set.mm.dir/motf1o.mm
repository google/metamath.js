include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cismt.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "ismot.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"

theorem motf1o
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motco.2: |- ( ph -> F e. ( G Ismt G ) )


  assert |- ( ph -> F : P -1-1-onto-> P )

  proof
    wph
    cP
    cP
    cF
    wf1o
    #
    va
    cv
    #
    cF
    cfv
    vb
    cv
    #
    cF
    cfv
    c.mi
    co
    @1
    @2
    c.mi
    co
    wceq
    vb
    cP
    wral
    va
    cP
    wral
    #
    wph
    cF
    cG
    cG
    cismt
    co
    wcel
    #
    @0
    @3
    wa
    #
    motco.2
    wph
    cG
    cV
    wcel
    @4
    @5
    wb
    motgrp.1
    cP
    cF
    cG
    c.mi
    cV
    va
    vb
    ismot.p
    ismot.m
    ismot
    syl
    mpbid
    simpld
end
