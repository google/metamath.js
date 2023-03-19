include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "caddc.mm"
include "cv.mm"
include "c1.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "clgam.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "id.mm"
include "lgamcvg2.mm"
include "lgamcvg.mm"
include "climuni.mm"
include "syl2anc.mm"

theorem lgamp1
  let cA: class A
  let vm: setvar m


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( log_G ` ( A + 1 ) ) = ( ( log_G ` A ) + ( log ` A ) ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    #
    caddc
    vm
    cn
    cA
    vm
    cv
    #
    c1
    caddc
    co
    @1
    cdiv
    co
    clog
    cfv
    cmul
    co
    cA
    @1
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
    #
    cA
    c1
    caddc
    co
    clgam
    cfv
    #
    cli
    wbr
    @3
    cA
    clgam
    cfv
    cA
    clog
    cfv
    caddc
    co
    #
    cli
    wbr
    @4
    @5
    wceq
    @0
    cA
    vm
    @2
    @2
    eqid
    #
    @0
    id
    #
    lgamcvg2
    @0
    cA
    vm
    @2
    @6
    @7
    lgamcvg
    @4
    @5
    @3
    climuni
    syl2anc
end
