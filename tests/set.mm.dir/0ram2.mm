include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cn0.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "cc0.mm"
include "cram.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wss.mm"
include "frn.mm"
include "3ad2ant3.mm"
include "nn0ssz.mm"
include "syl6ss.mm"
include "nn0ssre.mm"
include "wfo.mm"
include "simp1.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "syl2anc.mm"
include "cdm.mm"
include "fdm.mm"
include "simp2.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "fimaxre.mm"
include "syl3anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "0ram.mm"
include "mpdan.mm"

theorem 0ram2
  let cR: class R
  let cF: class F
  let vb: setvar b
  let vd: setvar d
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let cC: class C
  let va: setvar a
  let vi: setvar i
  let cM: class M
  let vy: setvar y
  let cV: class V


  assert |- ( ( R e. Fin /\ R =/= (/) /\ F : R --> NN0 ) -> ( 0 Ramsey F ) = sup ( ran F , RR , < ) )

  proof
    cR
    cfn
    wcel
    #
    cR
    c0
    wne
    #
    cR
    cn0
    cF
    wf
    #
    w3a
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cF
    crn
    #
    wral
    #
    vx
    cz
    wrex
    #
    cc0
    cF
    cram
    co
    @4
    cr
    clt
    csup
    wceq
    @3
    @4
    cz
    wss
    @5
    vx
    @4
    wrex
    #
    @6
    @3
    @4
    cn0
    cz
    @2
    @0
    @4
    cn0
    wss
    @1
    cR
    cn0
    cF
    frn
    3ad2ant3
    #
    nn0ssz
    syl6ss
    @3
    @4
    cr
    wss
    @4
    cfn
    wcel
    #
    @4
    c0
    wne
    #
    @7
    @3
    @4
    cn0
    cr
    @8
    nn0ssre
    syl6ss
    @3
    @0
    cR
    @4
    cF
    wfo
    #
    @9
    @0
    @1
    @2
    simp1
    @3
    cF
    cR
    wfn
    #
    @11
    @2
    @0
    @12
    @1
    cR
    cn0
    cF
    ffn
    3ad2ant3
    cR
    cF
    dffn4
    sylib
    cR
    @4
    cF
    fofi
    syl2anc
    @3
    cF
    cdm
    #
    c0
    wne
    @10
    @3
    @13
    cR
    c0
    @2
    @0
    @13
    cR
    wceq
    @1
    cR
    cn0
    cF
    fdm
    3ad2ant3
    @0
    @1
    @2
    simp2
    eqnetrd
    @13
    c0
    @4
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    vx
    vy
    @4
    fimaxre
    syl3anc
    @5
    vx
    @4
    cz
    ssrexv
    sylc
    vx
    vy
    cR
    cF
    cfn
    0ram
    mpdan
end
