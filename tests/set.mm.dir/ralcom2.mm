include "weq.mm"
include "wal.mm"
include "wral.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "eleq1.mm"
include "sps.mm"
include "imbi1d.mm"
include "dral1.mm"
include "bicomd.mm"
include "df-ral.mm"
include "3bitr4g.mm"
include "imbi12d.mm"
include "biimpd.mm"
include "wn.mm"
include "wa.mm"
include "nfnae.mm"
include "nfra2.mm"
include "nfan.mm"
include "nfra1.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantr.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "nfan1.mm"
include "rsp2.mm"
include "ancomsd.mm"
include "expdimp.mm"
include "adantll.mm"
include "ralrimi.mm"
include "ex.mm"
include "pm2.61i.mm"

theorem ralcom2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A y
  disjoint A x
  assert |- ( A. x e. A A. y e. A ph -> A. y e. A A. x e. A ph )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wph
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wral
    #
    vy
    cA
    wral
    #
    wi
    @1
    @3
    @5
    @1
    vx
    cv
    #
    cA
    wcel
    #
    @2
    wi
    #
    vx
    wal
    vy
    cv
    #
    cA
    wcel
    #
    @4
    wi
    #
    vy
    wal
    @3
    @5
    @8
    @11
    vx
    vy
    @1
    @7
    @10
    @2
    @4
    @0
    @7
    @10
    wb
    vx
    @6
    @9
    cA
    eleq1
    sps
    #
    @1
    @10
    wph
    wi
    #
    vy
    wal
    #
    @7
    wph
    wi
    #
    vx
    wal
    #
    @2
    @4
    @1
    @16
    @14
    @15
    @13
    vx
    vy
    @1
    @7
    @10
    wph
    @12
    imbi1d
    dral1
    bicomd
    wph
    vy
    cA
    df-ral
    wph
    vx
    cA
    df-ral
    3bitr4g
    imbi12d
    dral1
    @2
    vx
    cA
    df-ral
    @4
    vy
    cA
    df-ral
    3bitr4g
    biimpd
    @1
    wn
    #
    @3
    @5
    @17
    @3
    wa
    #
    @4
    vy
    cA
    @17
    @3
    vy
    vx
    vy
    vy
    nfnae
    wph
    vx
    vy
    cA
    cA
    nfra2
    nfan
    @18
    @10
    @4
    @18
    @10
    wa
    wph
    vx
    cA
    @18
    @10
    vx
    @17
    @3
    vx
    vx
    vy
    vx
    nfnae
    @2
    vx
    cA
    nfra1
    nfan
    @18
    vx
    @9
    cA
    @17
    vx
    @9
    wnfc
    @3
    vx
    vy
    nfcvf
    adantr
    @18
    vx
    cA
    nfcvd
    nfeld
    nfan1
    @3
    @10
    @15
    @17
    @3
    @10
    @7
    wph
    @3
    @7
    @10
    wph
    wph
    vx
    vy
    cA
    cA
    rsp2
    ancomsd
    expdimp
    adantll
    ralrimi
    ex
    ralrimi
    ex
    pm2.61i
end
