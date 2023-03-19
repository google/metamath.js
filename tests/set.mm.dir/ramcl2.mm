include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cram.mm"
include "co.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "cmap.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "c0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "eqid.mm"
include "ramcl2lem.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "ssun2.mm"
include "pnfex.mm"
include "snss.mm"
include "mpbir.mm"
include "syl6eqel.mm"
include "wne.mm"
include "ssun1.mm"
include "ramtcl2.mm"
include "biimpar.mm"
include "sseldi.mm"
include "pm2.61dane.mm"

theorem ramcl2
  let cR: class R
  let cF: class F
  let cM: class M
  let cV: class V
  let vc: setvar c
  let vf: setvar f
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vi: setvar i


  assert |- ( ( M e. NN0 /\ R e. V /\ F : R --> NN0 ) -> ( M Ramsey F ) e. ( NN0 u. { +oo } ) )

  proof
    cM
    cn0
    wcel
    cR
    cV
    wcel
    cR
    cn0
    cF
    wf
    w3a
    #
    cM
    cF
    cram
    co
    #
    cn0
    cpnf
    csn
    #
    cun
    #
    wcel
    vn
    cv
    vs
    cv
    #
    chash
    cfv
    cle
    wbr
    vc
    cv
    #
    cF
    cfv
    vx
    cv
    #
    chash
    cfv
    cle
    wbr
    @6
    cM
    va
    vi
    cvv
    cn0
    vb
    cv
    chash
    cfv
    vi
    cv
    wceq
    vb
    va
    cv
    cpw
    crab
    cmpt2
    #
    co
    vf
    cv
    ccnv
    @5
    csn
    cima
    wss
    wa
    vx
    @4
    cpw
    wrex
    vc
    cR
    wrex
    vf
    cR
    @4
    cM
    @7
    co
    cmap
    co
    wral
    wi
    vs
    wal
    vn
    cn0
    crab
    #
    c0
    @0
    @8
    c0
    wceq
    #
    wa
    @1
    cpnf
    @3
    @0
    @9
    @1
    @9
    cpnf
    @8
    cr
    clt
    cinf
    #
    cif
    cpnf
    vx
    @7
    cR
    @8
    vf
    vi
    vn
    cF
    cM
    cV
    vs
    va
    vb
    vc
    @7
    eqid
    #
    @8
    eqid
    #
    ramcl2lem
    @9
    cpnf
    @10
    iftrue
    sylan9eq
    cpnf
    @3
    wcel
    @2
    @3
    wss
    @2
    cn0
    ssun2
    cpnf
    @3
    pnfex
    snss
    mpbir
    syl6eqel
    @0
    @8
    c0
    wne
    #
    wa
    cn0
    @3
    @1
    cn0
    @2
    ssun1
    @0
    @1
    cn0
    wcel
    @13
    vx
    @7
    cR
    @8
    vf
    vi
    vn
    cF
    cM
    cV
    vs
    va
    vb
    vc
    @11
    @12
    ramtcl2
    biimpar
    sseldi
    pm2.61dane
end
