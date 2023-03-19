include "crg.mm"
include "wcel.mm"
include "cps1.mm"
include "cfv.mm"
include "cbs.mm"
include "co.mm"
include "cco1.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "id.mm"
include "ply1bascl.mm"
include "eqid.mm"
include "c1o.mm"
include "cmps.mm"
include "cmulr.mm"
include "cmpl.mm"
include "ply1mulr.mm"
include "mplmulr.mm"
include "psr1mulr.mm"
include "eqtr4i.mm"
include "coe1mul2.mm"
include "syl3an.mm"

theorem coe1mul
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cY: class Y
  assume coe1mul.s: |- Y = ( Poly1 ` R )
  assume coe1mul.t: |- .xb = ( .r ` Y )
  assume coe1mul.u: |- .x. = ( .r ` R )
  assume coe1mul.b: |- B = ( Base ` Y )

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G k
  disjoint G x
  disjoint R k
  disjoint R x
  disjoint .xb k
  disjoint .x. k
  disjoint .x. x
  assert |- ( ( R e. Ring /\ F e. B /\ G e. B ) -> ( coe1 ` ( F .xb G ) ) = ( k e. NN0 |-> ( R gsum ( x e. ( 0 ... k ) |-> ( ( ( coe1 ` F ) ` x ) .x. ( ( coe1 ` G ) ` ( k - x ) ) ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    @0
    cF
    cB
    wcel
    cF
    cR
    cps1
    cfv
    #
    cbs
    cfv
    #
    wcel
    cG
    cB
    wcel
    cG
    @2
    wcel
    cF
    cG
    c.xb
    co
    cco1
    cfv
    vk
    cn0
    cR
    vx
    cc0
    vk
    cv
    #
    cfz
    co
    vx
    cv
    #
    cF
    cco1
    cfv
    cfv
    @3
    @4
    cmin
    co
    cG
    cco1
    cfv
    cfv
    c.x
    co
    cmpt
    cgsu
    co
    cmpt
    wceq
    @0
    id
    cB
    cY
    cR
    cF
    coe1mul.s
    coe1mul.b
    ply1bascl
    cB
    cY
    cR
    cG
    coe1mul.s
    coe1mul.b
    ply1bascl
    vx
    @2
    cR
    @1
    c.xb
    c.x
    vk
    cF
    cG
    @1
    eqid
    #
    c.xb
    c1o
    cR
    cmps
    co
    #
    cmulr
    cfv
    @1
    cmulr
    cfv
    #
    cR
    @6
    c.xb
    c1o
    c1o
    cR
    cmpl
    co
    #
    @8
    eqid
    #
    @6
    eqid
    #
    cR
    @8
    c.xb
    cY
    coe1mul.s
    @9
    coe1mul.t
    ply1mulr
    mplmulr
    cR
    @6
    @7
    @1
    @5
    @10
    @7
    eqid
    psr1mulr
    eqtr4i
    coe1mul.u
    @2
    eqid
    coe1mul2
    syl3an
end
