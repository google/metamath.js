include "cc.mm"
include "wss.mm"
include "catan.mm"
include "cres.mm"
include "wf.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "ssid.mm"
include "ci.mm"
include "cneg.mm"
include "cpr.mm"
include "cdif.mm"
include "atanf.mm"
include "cdm.mm"
include "atansssdm.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "fssres.mm"
include "mp2an.mm"
include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "w3a.mm"
include "cdv.mm"
include "wceq.mm"
include "cdiv.mm"
include "ovex.mm"
include "dvatan.mm"
include "dmmpti.mm"
include "dvcn.mm"
include "mpan2.mm"
include "mp3an.mm"

theorem atancn
  let vy: setvar y
  let cD: class D
  let cS: class S
  let cA: class A
  let vx: setvar x
  assume atansopn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume atansopn.s: |- S = { y e. CC | ( 1 + ( y ^ 2 ) ) e. D }

  disjoint D y
  disjoint A y
  disjoint x y
  disjoint D x
  disjoint S x
  assert |- ( arctan |` S ) e. ( S -cn-> CC )

  proof
    cc
    cc
    wss
    #
    cS
    cc
    catan
    cS
    cres
    #
    wf
    #
    cS
    cc
    wss
    #
    @1
    cS
    cc
    ccncf
    co
    wcel
    #
    cc
    ssid
    cc
    ci
    cneg
    ci
    cpr
    cdif
    #
    cc
    catan
    wf
    cS
    @5
    wss
    @2
    atanf
    cS
    catan
    cdm
    @5
    vy
    cD
    cS
    atansopn.d
    atansopn.s
    atansssdm
    @5
    cc
    catan
    atanf
    fdmi
    sseqtri
    @5
    cc
    cS
    catan
    fssres
    mp2an
    cS
    c1
    vy
    cv
    c2
    cexp
    co
    caddc
    co
    cD
    wcel
    #
    vy
    cc
    crab
    cc
    atansopn.s
    @6
    vy
    cc
    ssrab2
    eqsstri
    @0
    @2
    @3
    w3a
    cc
    @1
    cdv
    co
    #
    cdm
    cS
    wceq
    @4
    vx
    cS
    c1
    c1
    vx
    cv
    c2
    cexp
    co
    caddc
    co
    #
    cdiv
    co
    @7
    c1
    @8
    cdiv
    ovex
    vx
    vy
    cD
    cS
    atansopn.d
    atansopn.s
    dvatan
    dmmpti
    cS
    cc
    @1
    dvcn
    mpan2
    mp3an
end
