include "wcel.mm"
include "cwunm.mm"
include "cfv.mm"
include "cwun.mm"
include "wss.mm"
include "wunccl.mm"
include "ssid.mm"
include "wuncss.mm"
include "sylancl.mm"
include "wuncid.mm"
include "syl.mm"
include "eqssd.mm"

theorem wuncidm
  let cA: class A
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cU: class U
  let cF: class F


  assert |- ( A e. V -> ( wUniCl ` ( wUniCl ` A ) ) = ( wUniCl ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cwunm
    cfv
    #
    cwunm
    cfv
    #
    @1
    @0
    @1
    cwun
    wcel
    #
    @1
    @1
    wss
    @2
    @1
    wss
    cA
    cV
    wunccl
    #
    @1
    ssid
    @1
    @1
    wuncss
    sylancl
    @0
    @3
    @1
    @2
    wss
    @4
    @1
    cwun
    wuncid
    syl
    eqssd
end
