include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cric.mm"
include "wbr.mm"
include "cpm2mp.mm"
include "eqid.mm"
include "pm2mprngiso.mm"
include "ne0i.mm"
include "syl.mm"
include "brric.mm"
include "sylibr.mm"

theorem pmmpric
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cN: class N
  assume pmmpric.p: |- P = ( Poly1 ` R )
  assume pmmpric.c: |- C = ( N Mat P )
  assume pmmpric.a: |- A = ( N Mat R )
  assume pmmpric.q: |- Q = ( Poly1 ` A )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> C ~=r Q )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cC
    cQ
    crs
    co
    #
    c0
    wne
    #
    cC
    cQ
    cric
    wbr
    @0
    cN
    cR
    cpm2mp
    co
    #
    @1
    wcel
    @2
    cA
    cC
    cP
    cQ
    cR
    @3
    cN
    pmmpric.p
    pmmpric.c
    pmmpric.a
    pmmpric.q
    @3
    eqid
    pm2mprngiso
    @1
    @3
    ne0i
    syl
    cC
    cQ
    brric
    sylibr
end
