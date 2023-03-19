include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "cgam.mm"
include "wf.mm"
include "ce.mm"
include "clgam.mm"
include "ccom.mm"
include "eff.mm"
include "lgamf.mm"
include "fco.mm"
include "mp2an.mm"
include "df-gam.mm"
include "feq1i.mm"
include "mpbir.mm"

theorem gamf
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cA: class A


  assert |- _G : ( CC \ ( ZZ \ NN ) ) --> CC

  proof
    cc
    cz
    cn
    cdif
    cdif
    #
    cc
    cgam
    wf
    @0
    cc
    ce
    clgam
    ccom
    #
    wf
    #
    cc
    cc
    ce
    wf
    @0
    cc
    clgam
    wf
    @2
    eff
    lgamf
    @0
    cc
    cc
    ce
    clgam
    fco
    mp2an
    @0
    cc
    cgam
    @1
    df-gam
    feq1i
    mpbir
end
