include "cn.mm"
include "wcel.mm"
include "c6.mm"
include "c4.mm"
include "cdc.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "cprime.mm"
include "wrex.mm"
include "bpos1.mm"
include "wn.mm"
include "csqrt.mm"
include "cfv.mm"
include "crp.mm"
include "clog.mm"
include "cdiv.mm"
include "cmpt.mm"
include "c9.mm"
include "caddc.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "bposlem9.mm"
include "pm2.18da.mm"
include "cr.mm"
include "wo.mm"
include "nnre.mm"
include "6nn0.mm"
include "4nn0.mm"
include "deccl.mm"
include "nn0rei.mm"
include "lelttric.mm"
include "sylancl.mm"
include "mpjaodan.mm"

theorem bpos
  let cN: class N
  let vp: setvar p
  let vn: setvar n
  let vx: setvar x

  disjoint N p
  disjoint n p
  disjoint N n
  disjoint n x
  disjoint N x
  assert |- ( N e. NN -> E. p e. Prime ( N < p /\ p <_ ( 2 x. N ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c6
    c4
    cdc
    #
    cle
    wbr
    #
    cN
    vp
    cv
    #
    clt
    wbr
    @3
    c2
    cN
    cmul
    co
    cle
    wbr
    wa
    vp
    cprime
    wrex
    #
    @1
    cN
    clt
    wbr
    #
    cN
    vp
    bpos1
    @0
    @5
    wa
    #
    @4
    @6
    @4
    wn
    #
    wa
    @4
    vx
    vn
    vn
    cn
    c2
    csqrt
    cfv
    vn
    cv
    #
    csqrt
    cfv
    vx
    crp
    vx
    cv
    #
    clog
    cfv
    @9
    cdiv
    co
    cmpt
    #
    cfv
    cmul
    co
    c9
    c4
    cdiv
    co
    @8
    c2
    cdiv
    co
    @10
    cfv
    cmul
    co
    caddc
    co
    c2
    clog
    cfv
    c2
    @8
    cmul
    co
    csqrt
    cfv
    cdiv
    co
    caddc
    co
    cmpt
    #
    @10
    cN
    vp
    @11
    eqid
    @10
    eqid
    @0
    @5
    @7
    simpll
    @0
    @5
    @7
    simplr
    @6
    @7
    simpr
    bposlem9
    pm2.18da
    @0
    cN
    cr
    wcel
    @1
    cr
    wcel
    @2
    @5
    wo
    cN
    nnre
    @1
    c6
    c4
    6nn0
    4nn0
    deccl
    nn0rei
    cN
    @1
    lelttric
    sylancl
    mpjaodan
end
