include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cn0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wne.mm"
include "simpl.mm"
include "eldifi.mm"
include "adantl.mm"
include "eldifsni.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cxr.mm"
include "wf.mm"
include "deg1xrf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "difss.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funimass4.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem deg1n0ima
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.0: class .0.
  let vx: setvar x
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )
  assume deg1nn0cl.b: |- B = ( Base ` P )


  assert |- ( R e. Ring -> ( D " ( B \ { .0. } ) ) C_ NN0 )

  proof
    cR
    crg
    wcel
    #
    vx
    cv
    #
    cD
    cfv
    cn0
    wcel
    #
    vx
    cB
    c.0
    csn
    #
    cdif
    #
    wral
    #
    cD
    @4
    cima
    cn0
    wss
    #
    @0
    @2
    vx
    @4
    @0
    @1
    @4
    wcel
    #
    wa
    @0
    @1
    cB
    wcel
    #
    @1
    c.0
    wne
    #
    @2
    @0
    @7
    simpl
    @7
    @8
    @0
    @1
    cB
    @3
    eldifi
    adantl
    @7
    @9
    @0
    @1
    cB
    c.0
    eldifsni
    adantl
    cB
    cD
    cP
    cR
    @1
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    deg1nn0cl
    syl3anc
    ralrimiva
    cD
    wfun
    #
    @4
    cD
    cdm
    #
    wss
    @6
    @5
    wb
    cB
    cxr
    cD
    wf
    @10
    cB
    cD
    cP
    cR
    deg1z.d
    deg1z.p
    deg1nn0cl.b
    deg1xrf
    #
    cB
    cxr
    cD
    ffun
    ax-mp
    @4
    cB
    @11
    cB
    @3
    difss
    cB
    cxr
    cD
    @12
    fdmi
    sseqtr4i
    vx
    @4
    cn0
    cD
    funimass4
    mp2an
    sylibr
end
