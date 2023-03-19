include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "clgam.mm"
include "wf.mm"
include "wtru.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "csu.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ovexd.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-lgam.mm"
include "a1i.mm"
include "lgamcl.mm"
include "adantl.mm"
include "fmpt2d.mm"
include "trud.mm"

theorem lgamf
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cA: class A


  assert |- log_G : ( CC \ ( ZZ \ NN ) ) --> CC

  proof
    cc
    cz
    cn
    cdif
    cdif
    #
    cc
    clgam
    wf
    wtru
    vx
    vx
    @0
    cn
    vx
    cv
    #
    vn
    cv
    #
    c1
    caddc
    co
    @2
    cdiv
    co
    clog
    cfv
    cmul
    co
    @1
    @2
    cdiv
    co
    c1
    caddc
    co
    clog
    cfv
    cmin
    co
    vn
    csu
    #
    @1
    clog
    cfv
    #
    cmin
    co
    #
    cc
    clgam
    cvv
    wtru
    @1
    @0
    wcel
    #
    wa
    @3
    @4
    cmin
    ovexd
    clgam
    vx
    @0
    @5
    cmpt
    wceq
    wtru
    vx
    vn
    df-lgam
    a1i
    @6
    @1
    clgam
    cfv
    cc
    wcel
    wtru
    @1
    lgamcl
    adantl
    fmpt2d
    trud
end
