include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "cco1.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "crab.mm"
include "eqid.mm"
include "cpmat.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "cur.mm"
include "1elcpmat.mm"
include "ne0i.mm"
include "syl.mm"
include "cpmatacl.mm"
include "cpmatinvcl.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "pmatring.mm"
include "ringgrp.mm"
include "issubg2.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem cpmatsubgpmat
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  assume cpmatsrngpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmatsrngpmat.p: |- P = ( Poly1 ` R )
  assume cpmatsrngpmat.c: |- C = ( N Mat P )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( SubGrp ` C ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cS
    cC
    csubg
    cfv
    wcel
    #
    cS
    cC
    cbs
    cfv
    #
    wss
    #
    cS
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    cC
    cplusg
    cfv
    #
    co
    cS
    wcel
    vy
    cS
    wral
    #
    @5
    cC
    cminusg
    cfv
    #
    cfv
    cS
    wcel
    #
    wa
    vx
    cS
    wral
    #
    @0
    cS
    vk
    cv
    vi
    cv
    vj
    cv
    vm
    cv
    co
    cco1
    cfv
    cfv
    cR
    c0g
    cfv
    wceq
    vk
    cn
    wral
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vm
    @2
    crab
    @2
    @2
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    vm
    cN
    crg
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @2
    eqid
    #
    cpmat
    @11
    vm
    @2
    ssrab2
    syl6eqss
    @0
    cC
    cur
    cfv
    #
    cS
    wcel
    @4
    cC
    cP
    cR
    cS
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    1elcpmat
    cS
    @13
    ne0i
    syl
    @0
    @7
    vx
    cS
    wral
    @9
    vx
    cS
    wral
    @10
    vx
    vy
    cC
    cP
    cR
    cS
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    cpmatacl
    vx
    cC
    cP
    cR
    cS
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    cpmatinvcl
    @7
    @9
    vx
    cS
    r19.26
    sylanbrc
    @0
    cC
    crg
    wcel
    cC
    cgrp
    wcel
    @1
    @3
    @4
    @10
    w3a
    wb
    cC
    cP
    cR
    cN
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    pmatring
    cC
    ringgrp
    vx
    vy
    @2
    @6
    cS
    cC
    @8
    @12
    @6
    eqid
    @8
    eqid
    issubg2
    3syl
    mpbir3and
end
