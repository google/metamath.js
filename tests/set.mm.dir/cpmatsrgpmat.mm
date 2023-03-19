include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "cpmatsubgpmat.mm"
include "1elcpmat.mm"
include "cpmatmcl.mm"
include "w3a.mm"
include "wb.mm"
include "pmatring.mm"
include "cbs.mm"
include "eqid.mm"
include "issubrg2.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem cpmatsrgpmat
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( SubRing ` C ) )

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
    csubrg
    cfv
    wcel
    #
    cS
    cC
    csubg
    cfv
    wcel
    #
    cC
    cur
    cfv
    #
    cS
    wcel
    #
    vx
    cv
    vy
    cv
    cC
    cmulr
    cfv
    #
    co
    cS
    wcel
    vy
    cS
    wral
    vx
    cS
    wral
    #
    cC
    cP
    cR
    cS
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    cpmatsubgpmat
    cC
    cP
    cR
    cS
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    1elcpmat
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
    cpmatmcl
    @0
    cC
    crg
    wcel
    @1
    @2
    @4
    @6
    w3a
    wb
    cC
    cP
    cR
    cN
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    pmatring
    vx
    vy
    cS
    cC
    cbs
    cfv
    #
    cC
    @5
    @3
    @7
    eqid
    @3
    eqid
    @5
    eqid
    issubrg2
    syl
    mpbir3and
end
