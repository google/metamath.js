include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "cram.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "crn.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "ad2antlr.mm"
include "wb.mm"
include "foeq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "fo00.mm"
include "simplbi.mm"
include "syl.mm"
include "oveq2d.mm"
include "0nn0.mm"
include "ram0.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "wne.mm"
include "w3a.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "0ram2.mm"
include "wss.mm"
include "frn.mm"
include "3ad2ant3.mm"
include "cz.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "nn0ssz.mm"
include "syl6ss.mm"
include "cdm.mm"
include "fdm.mm"
include "simp2.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "nn0ssre.mm"
include "simp1.mm"
include "fofi.mm"
include "syl2anc.mm"
include "fimaxre.mm"
include "syl3anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "suprzcl2.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "3expa.mm"
include "an32s.mm"
include "pm2.61dane.mm"

theorem 0ramcl
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


  assert |- ( ( R e. Fin /\ F : R --> NN0 ) -> ( 0 Ramsey F ) e. NN0 )

  proof
    cR
    cfn
    wcel
    #
    cR
    cn0
    cF
    wf
    #
    wa
    #
    cc0
    cF
    cram
    co
    #
    cn0
    wcel
    #
    cR
    c0
    @2
    cR
    c0
    wceq
    #
    wa
    #
    @3
    cc0
    c0
    cram
    co
    #
    cn0
    @6
    cF
    c0
    cc0
    cram
    @6
    c0
    cF
    crn
    #
    cF
    wfo
    #
    cF
    c0
    wceq
    #
    @6
    cR
    @8
    cF
    wfo
    #
    @9
    @1
    @11
    @0
    @5
    @1
    cF
    cR
    wfn
    @11
    cR
    cn0
    cF
    ffn
    cR
    cF
    dffn4
    sylib
    #
    ad2antlr
    @5
    @11
    @9
    wb
    @2
    cR
    c0
    @8
    cF
    foeq2
    adantl
    mpbid
    @9
    @10
    @8
    c0
    wceq
    @8
    cF
    fo00
    simplbi
    syl
    oveq2d
    @7
    cc0
    cn0
    cc0
    cn0
    wcel
    @7
    cc0
    wceq
    0nn0
    cc0
    ram0
    ax-mp
    0nn0
    eqeltri
    syl6eqel
    @0
    cR
    c0
    wne
    #
    @1
    @4
    @0
    @13
    @1
    @4
    @0
    @13
    @1
    w3a
    #
    @3
    @8
    cr
    clt
    csup
    #
    cn0
    cR
    cF
    0ram2
    @14
    @8
    cn0
    @15
    @1
    @0
    @8
    cn0
    wss
    @13
    cR
    cn0
    cF
    frn
    3ad2ant3
    #
    @14
    @8
    cz
    wss
    #
    @8
    c0
    wne
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    @8
    wral
    #
    vx
    cz
    wrex
    #
    @15
    @8
    wcel
    @14
    @8
    cn0
    cz
    @16
    nn0ssz
    syl6ss
    #
    @14
    cF
    cdm
    #
    c0
    wne
    @18
    @14
    @22
    cR
    c0
    @1
    @0
    @22
    cR
    wceq
    @13
    cR
    cn0
    cF
    fdm
    3ad2ant3
    @0
    @13
    @1
    simp2
    eqnetrd
    @22
    c0
    @8
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    #
    @14
    @17
    @19
    vx
    @8
    wrex
    #
    @20
    @21
    @14
    @8
    cr
    wss
    @8
    cfn
    wcel
    #
    @18
    @24
    @14
    @8
    cn0
    cr
    @16
    nn0ssre
    syl6ss
    @14
    @0
    @11
    @25
    @0
    @13
    @1
    simp1
    @1
    @0
    @11
    @13
    @12
    3ad2ant3
    cR
    @8
    cF
    fofi
    syl2anc
    @23
    vx
    vy
    @8
    fimaxre
    syl3anc
    @19
    vx
    @8
    cz
    ssrexv
    sylc
    vx
    vy
    @8
    suprzcl2
    syl3anc
    sseldd
    eqeltrd
    3expa
    an32s
    pm2.61dane
end
