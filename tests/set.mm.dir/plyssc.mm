include "cply.mm"
include "cfv.mm"
include "cc.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "plybss.mm"
include "ssid.mm"
include "plyss.mm"
include "sylancl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "pm2.61ine.mm"

theorem plyssc
  let cS: class S
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cT: class T
  let cF: class F


  assert |- ( Poly ` S ) C_ ( Poly ` CC )

  proof
    cS
    cply
    cfv
    #
    cc
    cply
    cfv
    #
    wss
    #
    @0
    c0
    @0
    c0
    wceq
    @2
    c0
    @1
    wss
    @1
    0ss
    @0
    c0
    @1
    sseq1
    mpbiri
    @0
    c0
    wne
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    n0
    @4
    @2
    vf
    @4
    cS
    cc
    wss
    cc
    cc
    wss
    @2
    cS
    @3
    plybss
    cc
    ssid
    cS
    cc
    plyss
    sylancl
    exlimiv
    sylbi
    pm2.61ine
end
