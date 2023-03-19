include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "reldom.mm"
include "brrelexi.mm"
include "cv.mm"
include "wceq.mm"
include "breq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "wss.mm"
include "cima.mm"
include "cdif.mm"
include "cab.mm"
include "cuni.mm"
include "cres.mm"
include "ccnv.mm"
include "cun.mm"
include "vex.mm"
include "sseq1.mm"
include "imaeq2.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "difeq2.mm"
include "sseq12d.mm"
include "cbvabv.mm"
include "eqid.mm"
include "sbthlem10.mm"
include "vtocl2g.mm"
include "syl2an.mm"
include "pm2.43i.mm"

theorem sbth
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( A ~<_ B /\ B ~<_ A ) -> A ~~ B )

  proof
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    cB
    cen
    wbr
    #
    @0
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @2
    @3
    wi
    #
    @1
    cA
    cB
    cdom
    reldom
    brrelexi
    cB
    cA
    cdom
    reldom
    brrelexi
    vz
    cv
    #
    vw
    cv
    #
    cdom
    wbr
    #
    @6
    @5
    cdom
    wbr
    #
    wa
    #
    @5
    @6
    cen
    wbr
    #
    wi
    cA
    @6
    cdom
    wbr
    #
    @6
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    @6
    cen
    wbr
    #
    wi
    @4
    vz
    vw
    cA
    cB
    cvv
    cvv
    @5
    cA
    wceq
    #
    @9
    @13
    @10
    @14
    @15
    @7
    @11
    @8
    @12
    @5
    cA
    @6
    cdom
    breq1
    @5
    cA
    @6
    cdom
    breq2
    anbi12d
    @5
    cA
    @6
    cen
    breq1
    imbi12d
    @6
    cB
    wceq
    #
    @13
    @2
    @14
    @3
    @16
    @11
    @0
    @12
    @1
    @6
    cB
    cA
    cdom
    breq2
    @6
    cB
    cA
    cdom
    breq1
    anbi12d
    @6
    cB
    cA
    cen
    breq2
    imbi12d
    vx
    @5
    @6
    vy
    cv
    #
    @5
    wss
    #
    vg
    cv
    #
    @6
    vf
    cv
    #
    @17
    cima
    #
    cdif
    #
    cima
    #
    @5
    @17
    cdif
    #
    wss
    #
    wa
    #
    vy
    cab
    #
    vf
    vg
    @20
    @27
    cuni
    #
    cres
    @19
    ccnv
    @5
    @28
    cdif
    cres
    cun
    #
    vz
    vex
    @26
    vx
    cv
    #
    @5
    wss
    #
    @19
    @6
    @20
    @30
    cima
    #
    cdif
    #
    cima
    #
    @5
    @30
    cdif
    #
    wss
    #
    wa
    vy
    vx
    @17
    @30
    wceq
    #
    @18
    @31
    @25
    @36
    @17
    @30
    @5
    sseq1
    @37
    @23
    @34
    @24
    @35
    @37
    @22
    @33
    @19
    @37
    @21
    @32
    @6
    @17
    @30
    @20
    imaeq2
    difeq2d
    imaeq2d
    @17
    @30
    @5
    difeq2
    sseq12d
    anbi12d
    cbvabv
    @29
    eqid
    vw
    vex
    sbthlem10
    vtocl2g
    syl2an
    pm2.43i
end
