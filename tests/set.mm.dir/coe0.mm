include "c0p.mm"
include "ccoe.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wtru.mm"
include "cc.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "wcel.mm"
include "cply.mm"
include "0cnd.mm"
include "wss.mm"
include "ssid.mm"
include "ply0.mm"
include "ax-mp.mm"
include "coemulc.mm"
include "sylancl.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "wf.mm"
include "plyf.mm"
include "mp1i.mm"
include "cv.mm"
include "mul02.mm"
include "adantl.mm"
include "caofid2.mm"
include "df-0p.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "nn0ex.mm"
include "eqid.mm"
include "coef3.mm"
include "3eqtr3d.mm"
include "trud.mm"

theorem coe0
  let vk: setvar k
  let vn: setvar n
  let cA: class A
  let cF: class F
  let cS: class S
  let vx: setvar x


  assert |- ( coeff ` 0p ) = ( NN0 X. { 0 } )

  proof
    c0p
    ccoe
    cfv
    #
    cn0
    cc0
    csn
    #
    cxp
    #
    wceq
    wtru
    cc
    @1
    cxp
    #
    c0p
    cmul
    cof
    #
    co
    #
    ccoe
    cfv
    #
    @2
    @0
    @4
    co
    #
    @0
    @2
    wtru
    cc0
    cc
    wcel
    c0p
    cc
    cply
    cfv
    wcel
    #
    @6
    @7
    wceq
    wtru
    0cnd
    #
    cc
    cc
    wss
    @8
    cc
    ssid
    cc
    ply0
    ax-mp
    #
    cc0
    cc
    c0p
    coemulc
    sylancl
    wtru
    @5
    c0p
    ccoe
    wtru
    @5
    @3
    c0p
    wtru
    vx
    cc
    cc0
    cc0
    cmul
    cc
    c0p
    cvv
    cc
    cc
    cc
    cvv
    wcel
    wtru
    cnex
    a1i
    @8
    cc
    cc
    c0p
    wf
    wtru
    @10
    cc
    c0p
    plyf
    mp1i
    @9
    @9
    vx
    cv
    #
    cc
    wcel
    cc0
    @11
    cmul
    co
    cc0
    wceq
    wtru
    @11
    mul02
    adantl
    #
    caofid2
    df-0p
    syl6eqr
    fveq2d
    wtru
    vx
    cn0
    cc0
    cc0
    cmul
    cc
    @0
    cvv
    cc
    cc
    cn0
    cvv
    wcel
    wtru
    nn0ex
    a1i
    @8
    cn0
    cc
    @0
    wf
    wtru
    @10
    @0
    cc
    c0p
    @0
    eqid
    coef3
    mp1i
    @9
    @9
    @12
    caofid2
    3eqtr3d
    trud
end
