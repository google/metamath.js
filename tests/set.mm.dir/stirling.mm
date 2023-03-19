include "cn.mm"
include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "ceu.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "crp.mm"
include "wrex.mm"
include "c1.mm"
include "clog.mm"
include "eqid.mm"
include "stirlinglem14.mm"
include "wcel.mm"
include "wa.mm"
include "c4.mm"
include "caddc.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfan.mm"
include "simpl.mm"
include "simpr.mm"
include "stirlinglem15.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem stirling
  let cS: class S
  let vn: setvar n
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume stirling.1: |- S = ( n e. NN0 |-> ( ( sqrt ` ( ( 2 x. _pi ) x. n ) ) x. ( ( n / _e ) ^ n ) ) )


  assert |- ( n e. NN |-> ( ( ! ` n ) / ( S ` n ) ) ) ~~> 1

  proof
    vn
    cn
    vn
    cv
    #
    cfa
    cfv
    #
    c2
    @0
    cmul
    co
    #
    csqrt
    cfv
    @0
    ceu
    cdiv
    co
    @0
    cexp
    co
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    vc
    cv
    #
    cli
    wbr
    #
    vc
    crp
    wrex
    vn
    cn
    @1
    @0
    cS
    cfv
    cdiv
    co
    cmpt
    c1
    cli
    wbr
    #
    @5
    vn
    cn
    @0
    @5
    cfv
    #
    clog
    cfv
    cmpt
    #
    vn
    vc
    @5
    eqid
    #
    @10
    eqid
    stirlinglem14
    @7
    @8
    vc
    crp
    @6
    crp
    wcel
    #
    @7
    wa
    @5
    @6
    vn
    cn
    @2
    @5
    cfv
    cmpt
    #
    cS
    vn
    vn
    cn
    @3
    cmpt
    #
    vn
    cn
    @9
    c4
    cexp
    co
    @0
    @13
    cfv
    c2
    cexp
    co
    cdiv
    co
    cmpt
    #
    vn
    cn
    @0
    c2
    cexp
    co
    @0
    @2
    c1
    caddc
    co
    #
    cmul
    co
    cdiv
    co
    cmpt
    #
    vn
    cn
    c2
    c4
    @0
    cmul
    co
    cexp
    co
    @1
    c4
    cexp
    co
    cmul
    co
    @2
    cfa
    cfv
    c2
    cexp
    co
    cdiv
    co
    @16
    cdiv
    co
    cmpt
    #
    @12
    @7
    vn
    @12
    vn
    nfv
    vn
    @5
    @6
    cli
    vn
    cn
    @4
    nfmpt1
    vn
    cli
    nfcv
    vn
    @6
    nfcv
    nfbr
    nfan
    stirling.1
    @11
    @13
    eqid
    @14
    eqid
    @18
    eqid
    @15
    eqid
    @17
    eqid
    @12
    @7
    simpl
    @12
    @7
    simpr
    stirlinglem15
    rexlimiva
    ax-mp
end
