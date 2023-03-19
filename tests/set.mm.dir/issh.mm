include "chil.mm"
include "cpw.mm"
include "wcel.mm"
include "c0v.mm"
include "cva.mm"
include "cxp.mm"
include "cima.mm"
include "wss.mm"
include "csm.mm"
include "cc.mm"
include "w3a.mm"
include "wa.mm"
include "csh.mm"
include "ax-hilex.mm"
include "elpw2.mm"
include "3anass.mm"
include "anbi12i.mm"
include "cv.mm"
include "wceq.mm"
include "eleq2.mm"
include "id.mm"
include "sqxpeqd.mm"
include "imaeq2d.mm"
include "sseq12d.mm"
include "xpeq2.mm"
include "3anbi123d.mm"
include "df-sh.mm"
include "elrab2.mm"
include "anass.mm"
include "3bitr4i.mm"

theorem issh
  let cH: class H
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y


  assert |- ( H e. SH <-> ( ( H C_ ~H /\ 0h e. H ) /\ ( ( +h " ( H X. H ) ) C_ H /\ ( .h " ( CC X. H ) ) C_ H ) ) )

  proof
    cH
    chil
    cpw
    #
    wcel
    #
    c0v
    cH
    wcel
    #
    cva
    cH
    cH
    cxp
    #
    cima
    #
    cH
    wss
    #
    csm
    cc
    cH
    cxp
    #
    cima
    #
    cH
    wss
    #
    w3a
    #
    wa
    cH
    chil
    wss
    #
    @2
    @5
    @8
    wa
    #
    wa
    #
    wa
    cH
    csh
    wcel
    @10
    @2
    wa
    @11
    wa
    @1
    @10
    @9
    @12
    cH
    chil
    ax-hilex
    elpw2
    @2
    @5
    @8
    3anass
    anbi12i
    c0v
    vh
    cv
    #
    wcel
    #
    cva
    @13
    @13
    cxp
    #
    cima
    #
    @13
    wss
    #
    csm
    cc
    @13
    cxp
    #
    cima
    #
    @13
    wss
    #
    w3a
    @9
    vh
    cH
    @0
    csh
    @13
    cH
    wceq
    #
    @14
    @2
    @17
    @5
    @20
    @8
    @13
    cH
    c0v
    eleq2
    @21
    @16
    @4
    @13
    cH
    @21
    @15
    @3
    cva
    @21
    @13
    cH
    @21
    id
    #
    sqxpeqd
    imaeq2d
    @22
    sseq12d
    @21
    @19
    @7
    @13
    cH
    @21
    @18
    @6
    csm
    @13
    cH
    cc
    xpeq2
    imaeq2d
    @22
    sseq12d
    3anbi123d
    vh
    df-sh
    elrab2
    @10
    @2
    @11
    anass
    3bitr4i
end
