include "csalg.mm"
include "wcel.mm"
include "c0.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "issal.mm"
include "ibi.mm"
include "simp1d.mm"

theorem 0sal
  let cS: class S
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x


  assert |- ( S e. SAlg -> (/) e. S )

  proof
    cS
    csalg
    wcel
    #
    c0
    cS
    wcel
    #
    cS
    cuni
    vy
    cv
    #
    cdif
    cS
    wcel
    vy
    cS
    wral
    #
    @2
    com
    cdom
    wbr
    @2
    cuni
    cS
    wcel
    wi
    vy
    cS
    cpw
    wral
    #
    @0
    @1
    @3
    @4
    w3a
    vy
    cS
    csalg
    issal
    ibi
    simp1d
end
