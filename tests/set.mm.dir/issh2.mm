include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cva.mm"
include "cxp.mm"
include "cima.mm"
include "csm.mm"
include "cc.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "issh.mm"
include "wb.mm"
include "wfun.mm"
include "cdm.mm"
include "wf.mm"
include "ax-hfvadd.mm"
include "ffun.mm"
include "ax-mp.mm"
include "xpss12.mm"
include "anidms.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "funimassov.mm"
include "sylancr.mm"
include "ax-hfvmul.mm"
include "xpss2.mm"
include "anbi12d.mm"
include "adantr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem issh2
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let vh: setvar h

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint h x
  disjoint h y
  disjoint H h
  assert |- ( H e. SH <-> ( ( H C_ ~H /\ 0h e. H ) /\ ( A. x e. H A. y e. H ( x +h y ) e. H /\ A. x e. CC A. y e. H ( x .h y ) e. H ) ) )

  proof
    cH
    csh
    wcel
    cH
    chil
    wss
    #
    c0v
    cH
    wcel
    #
    wa
    #
    cva
    cH
    cH
    cxp
    #
    cima
    cH
    wss
    #
    csm
    cc
    cH
    cxp
    #
    cima
    cH
    wss
    #
    wa
    #
    wa
    @2
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    cH
    wcel
    vy
    cH
    wral
    vx
    cH
    wral
    #
    @8
    @9
    csm
    co
    cH
    wcel
    vy
    cH
    wral
    vx
    cc
    wral
    #
    wa
    #
    wa
    cH
    issh
    @2
    @7
    @12
    @0
    @7
    @12
    wb
    @1
    @0
    @4
    @10
    @6
    @11
    @0
    cva
    wfun
    #
    @3
    cva
    cdm
    #
    wss
    @4
    @10
    wb
    chil
    chil
    cxp
    #
    chil
    cva
    wf
    @13
    ax-hfvadd
    @15
    chil
    cva
    ffun
    ax-mp
    @0
    @3
    @15
    @14
    @0
    @3
    @15
    wss
    cH
    chil
    cH
    chil
    xpss12
    anidms
    @15
    chil
    cva
    ax-hfvadd
    fdmi
    syl6sseqr
    vx
    vy
    cH
    cH
    cH
    cva
    funimassov
    sylancr
    @0
    csm
    wfun
    #
    @5
    csm
    cdm
    #
    wss
    @6
    @11
    wb
    cc
    chil
    cxp
    #
    chil
    csm
    wf
    @16
    ax-hfvmul
    @18
    chil
    csm
    ffun
    ax-mp
    @0
    @5
    @18
    @17
    cH
    chil
    cc
    xpss2
    @18
    chil
    csm
    ax-hfvmul
    fdmi
    syl6sseqr
    vx
    vy
    cc
    cH
    cH
    csm
    funimassov
    sylancr
    anbi12d
    adantr
    pm5.32i
    bitri
end
