include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf1o.mm"
include "cismt.mm"
include "wa.mm"
include "wb.mm"
include "ismot.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem motcgr
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  assume motcgr.a: |- ( ph -> A e. P )
  assume motcgr.b: |- ( ph -> B e. P )
  assume motcgr.f: |- ( ph -> F e. ( G Ismt G ) )


  assert |- ( ph -> ( ( F ` A ) .- ( F ` B ) ) = ( A .- B ) )

  proof
    wph
    cA
    cP
    wcel
    cB
    cP
    wcel
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    c.mi
    co
    #
    @0
    @2
    c.mi
    co
    #
    wceq
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    c.mi
    co
    #
    cA
    cB
    c.mi
    co
    #
    wceq
    #
    motcgr.a
    motcgr.b
    wph
    cP
    cP
    cF
    wf1o
    #
    @7
    wph
    cF
    cG
    cG
    cismt
    co
    wcel
    #
    @13
    @7
    wa
    #
    motcgr.f
    wph
    cG
    cV
    wcel
    @14
    @15
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
    simprd
    @6
    @12
    @8
    @3
    c.mi
    co
    #
    cA
    @2
    c.mi
    co
    #
    wceq
    va
    vb
    cA
    cB
    cP
    cP
    @0
    cA
    wceq
    #
    @4
    @16
    @5
    @17
    @18
    @1
    @8
    @3
    c.mi
    @0
    cA
    cF
    fveq2
    oveq1d
    @0
    cA
    @2
    c.mi
    oveq1
    eqeq12d
    @2
    cB
    wceq
    #
    @16
    @10
    @17
    @11
    @19
    @3
    @9
    @8
    c.mi
    @2
    cB
    cF
    fveq2
    oveq2d
    @2
    cB
    cA
    c.mi
    oveq2
    eqeq12d
    rspc2va
    syl21anc
end
