include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "clgam.mm"
include "cfv.mm"
include "caddc.mm"
include "cv.mm"
include "c1.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cabs.mm"
include "cle.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "eqid.mm"
include "id.mm"
include "lgamcvglem.mm"
include "simpld.mm"

theorem lgamcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( log_G ` A ) e. CC )

  proof
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    #
    cA
    clgam
    cfv
    #
    cc
    wcel
    caddc
    vn
    cn
    cA
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
    cA
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
    cmpt
    #
    c1
    cseq
    @1
    cA
    clog
    cfv
    caddc
    co
    cli
    wbr
    @0
    vx
    cA
    vx
    cv
    #
    cabs
    cfv
    vr
    cv
    #
    cle
    wbr
    c1
    @5
    cdiv
    co
    @4
    vk
    cv
    caddc
    co
    cabs
    cfv
    cle
    wbr
    vk
    cn0
    wral
    wa
    vx
    cc
    crab
    #
    vk
    vn
    @3
    vr
    @6
    eqid
    @0
    id
    @3
    eqid
    lgamcvglem
    simpld
end
