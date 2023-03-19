include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cismt.mm"
include "f1oi.mm"
include "a1i.mm"
include "wa.mm"
include "fvresi.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "ralrimivva.mm"
include "ismot.mm"
include "biimpar.mm"
include "syl12anc.mm"

theorem idmot
  let wph: wff ph
  let cP: class P
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )


  assert |- ( ph -> ( _I |` P ) e. ( G Ismt G ) )

  proof
    wph
    cG
    cV
    wcel
    #
    cP
    cP
    cid
    cP
    cres
    #
    wf1o
    #
    va
    cv
    #
    @1
    cfv
    #
    vb
    cv
    #
    @1
    cfv
    #
    c.mi
    co
    @3
    @5
    c.mi
    co
    wceq
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    @1
    cG
    cG
    cismt
    co
    wcel
    #
    motgrp.1
    @2
    wph
    cP
    f1oi
    a1i
    wph
    @7
    va
    vb
    cP
    cP
    wph
    @3
    cP
    wcel
    #
    @5
    cP
    wcel
    #
    wa
    wa
    @4
    @3
    @6
    @5
    c.mi
    @10
    @4
    @3
    wceq
    wph
    @11
    cP
    @3
    fvresi
    ad2antrl
    @11
    @6
    @5
    wceq
    wph
    @10
    cP
    @5
    fvresi
    ad2antll
    oveq12d
    ralrimivva
    @0
    @9
    @2
    @8
    wa
    cP
    @1
    cG
    c.mi
    cV
    va
    vb
    ismot.p
    ismot.m
    ismot
    biimpar
    syl12anc
end
