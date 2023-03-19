include "ctop.mm"
include "chmph.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "cxp.mm"
include "wss.mm"
include "chmeo.mm"
include "ccnv.mm"
include "cvv.mm"
include "c1o.mm"
include "cdif.mm"
include "cima.mm"
include "df-hmph.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "wceq.mm"
include "hmeofn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "hmphsym.mm"
include "adantl.mm"
include "wa.mm"
include "hmphtr.mm"
include "wcel.mm"
include "wb.mm"
include "hmphref.mm"
include "hmphtop1.mm"
include "impbii.mm"
include "iserd.mm"
include "trud.mm"

theorem hmpher
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let cJ: class J
  let cK: class K
  let cL: class L


  assert |- ~= Er Top

  proof
    ctop
    chmph
    wer
    wtru
    vx
    vy
    vz
    ctop
    chmph
    chmph
    wrel
    #
    wtru
    chmph
    ctop
    ctop
    cxp
    #
    wss
    @1
    wrel
    @0
    chmph
    chmeo
    ccnv
    cvv
    c1o
    cdif
    #
    cima
    #
    @1
    df-hmph
    @3
    chmeo
    cdm
    #
    @1
    chmeo
    @2
    cnvimass
    chmeo
    @1
    wfn
    @4
    @1
    wceq
    hmeofn
    @1
    chmeo
    fndm
    ax-mp
    sseqtri
    eqsstri
    ctop
    ctop
    relxp
    chmph
    @1
    relss
    mp2
    a1i
    vx
    cv
    #
    vy
    cv
    #
    chmph
    wbr
    #
    @6
    @5
    chmph
    wbr
    wtru
    @5
    @6
    hmphsym
    adantl
    @7
    @6
    vz
    cv
    #
    chmph
    wbr
    wa
    @5
    @8
    chmph
    wbr
    wtru
    @5
    @6
    @8
    hmphtr
    adantl
    @5
    ctop
    wcel
    #
    @5
    @5
    chmph
    wbr
    #
    wb
    wtru
    @9
    @10
    @5
    hmphref
    @5
    @5
    hmphtop1
    impbii
    a1i
    iserd
    trud
end
