include "cr.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "citg2.mm"
include "cfv.mm"
include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wceq.mm"
include "i1f0.mm"
include "wtru.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "wf.mm"
include "i1ff.mm"
include "ax-mp.mm"
include "cv.mm"
include "leid.mm"
include "adantl.mm"
include "caofref.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "0pledm.mm"
include "mpbird.mm"
include "trud.mm"
include "itg2itg1.mm"
include "mp2an.mm"
include "itg10.mm"
include "eqtri.mm"

theorem itg20
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cF: class F
  let cG: class G


  assert |- ( S.2 ` ( RR X. { 0 } ) ) = 0

  proof
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    #
    @0
    citg1
    cfv
    #
    cc0
    @0
    citg1
    cdm
    wcel
    #
    c0p
    @0
    cle
    cofr
    #
    wbr
    #
    @1
    @2
    wceq
    i1f0
    @5
    wtru
    @5
    @0
    @0
    @4
    wbr
    wtru
    vx
    cr
    cle
    cr
    @0
    cvv
    cr
    cvv
    wcel
    wtru
    reex
    a1i
    cr
    cr
    @0
    wf
    #
    wtru
    @3
    @6
    i1f0
    @0
    i1ff
    ax-mp
    a1i
    #
    vx
    cv
    #
    cr
    wcel
    @8
    @8
    cle
    wbr
    wtru
    @8
    leid
    adantl
    caofref
    wtru
    cr
    @0
    cr
    cc
    wss
    wtru
    ax-resscn
    a1i
    wtru
    @6
    @0
    cr
    wfn
    @7
    cr
    cr
    @0
    ffn
    syl
    0pledm
    mpbird
    trud
    @0
    itg2itg1
    mp2an
    itg10
    eqtri
end
