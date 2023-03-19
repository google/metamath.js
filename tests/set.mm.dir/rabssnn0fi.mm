include "cn0.mm"
include "crab.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wb.mm"
include "ssrab2.mm"
include "wnel.mm"
include "ssnn0fi.mm"
include "wa.mm"
include "wsbc.mm"
include "nnel.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfn.mm"
include "weq.mm"
include "sbceq2a.mm"
include "equcoms.mm"
include "con2bid.mm"
include "elrabf.mm"
include "baib.mm"
include "syl5bb.mm"
include "con4bid.mm"
include "imbi2d.mm"
include "ralbiia.mm"
include "nfv.mm"
include "nfim.mm"
include "breq2.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "bitri.mm"
include "a1i.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "ax-mp.mm"

theorem rabssnn0fi
  let wph: wff ph
  let vx: setvar x
  let vs: setvar s
  let vy: setvar y

  disjoint s x
  disjoint ph s
  disjoint s y
  disjoint x y
  disjoint ph y
  assert |- ( { x e. NN0 | ph } e. Fin <-> E. s e. NN0 A. x e. NN0 ( s < x -> -. ph ) )

  proof
    wph
    vx
    cn0
    crab
    #
    cn0
    wss
    #
    @0
    cfn
    wcel
    #
    vs
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wph
    wn
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    wb
    wph
    vx
    cn0
    ssrab2
    @1
    @2
    @3
    vy
    cv
    #
    clt
    wbr
    #
    @10
    @0
    wnel
    #
    wi
    #
    vy
    cn0
    wral
    #
    vs
    cn0
    wrex
    @9
    vy
    @0
    vs
    ssnn0fi
    @1
    @14
    @8
    vs
    cn0
    @14
    @8
    wb
    @1
    @3
    cn0
    wcel
    wa
    @14
    @11
    @6
    vx
    @10
    wsbc
    #
    wi
    #
    vy
    cn0
    wral
    @8
    @13
    @16
    vy
    cn0
    @10
    cn0
    wcel
    #
    @12
    @15
    @11
    @17
    @12
    @15
    @12
    wn
    @10
    @0
    wcel
    #
    @17
    @15
    wn
    #
    @10
    @0
    nnel
    @18
    @17
    @19
    wph
    @19
    vx
    @10
    cn0
    vx
    @10
    nfcv
    vx
    cn0
    nfcv
    @15
    vx
    @6
    vx
    @10
    nfsbc1v
    #
    nfn
    vx
    vy
    weq
    @15
    wph
    @15
    @6
    wb
    vy
    vx
    @6
    vx
    @10
    sbceq2a
    #
    equcoms
    con2bid
    elrabf
    baib
    syl5bb
    con4bid
    imbi2d
    ralbiia
    @16
    @7
    vy
    vx
    cn0
    @11
    @15
    vx
    @11
    vx
    nfv
    @20
    nfim
    @7
    vy
    nfv
    vy
    vx
    weq
    @11
    @5
    @15
    @6
    @10
    @4
    @3
    clt
    breq2
    @21
    imbi12d
    cbvral
    bitri
    a1i
    rexbidva
    bitrd
    ax-mp
end
