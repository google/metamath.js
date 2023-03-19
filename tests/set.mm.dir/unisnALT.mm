include "csn.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "eluni.mm"
include "biimpi.mm"
include "wceq.mm"
include "id.mm"
include "simpl.mm"
include "syl.mm"
include "simpr.mm"
include "elsni.mm"
include "eleq2.mm"
include "biimpac.mm"
include "syl2anc.mm"
include "ax-gen.mm"
include "19.23v.mm"
include "ax-mp.mm"
include "pm3.35.mm"
include "sylancl.mm"
include "dfss2.mm"
include "biimpri.mm"
include "snid.mm"
include "elunii.mm"
include "eqssi.mm"

theorem unisnALT
  let cA: class A
  let vq: setvar q
  let vx: setvar x
  assume unisnALT.1: |- A e. _V


  assert |- U. { A } = A

  proof
    cA
    csn
    #
    cuni
    #
    cA
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    @1
    cA
    wss
    #
    @5
    vx
    @3
    @2
    vq
    cv
    #
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    vq
    wex
    #
    @12
    @4
    wi
    #
    @4
    @3
    @12
    vq
    @2
    @0
    eluni
    biimpi
    @11
    @4
    wi
    #
    vq
    wal
    #
    @13
    @14
    vq
    @11
    @9
    @8
    cA
    wceq
    #
    @4
    @11
    @11
    @9
    @11
    id
    #
    @9
    @10
    simpl
    syl
    @11
    @10
    @16
    @11
    @11
    @10
    @17
    @9
    @10
    simpr
    syl
    @8
    cA
    elsni
    syl
    @16
    @9
    @4
    @8
    cA
    @2
    eleq2
    biimpac
    syl2anc
    ax-gen
    @15
    @13
    @11
    @4
    vq
    19.23v
    biimpi
    ax-mp
    @12
    @4
    pm3.35
    sylancl
    ax-gen
    @7
    @6
    vx
    @1
    cA
    dfss2
    biimpri
    ax-mp
    @4
    @3
    wi
    #
    vx
    wal
    #
    cA
    @1
    wss
    #
    @18
    vx
    @4
    @4
    cA
    @0
    wcel
    @3
    @4
    id
    cA
    unisnALT.1
    snid
    @2
    cA
    @0
    elunii
    sylancl
    ax-gen
    @20
    @19
    vx
    cA
    @1
    dfss2
    biimpri
    ax-mp
    eqssi
end
