include "clcv.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "islshpcv.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "l1cvat.mm"

theorem lshpat
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cW: class W
  assume lshpat.s: |- S = ( LSubSp ` W )
  assume lshpat.p: |- .(+) = ( LSSum ` W )
  assume ishpat.h: |- H = ( LSHyp ` W )
  assume lshpat.a: |- A = ( LSAtoms ` W )
  assume lshpat.w: |- ( ph -> W e. LVec )
  assume lshpat.l: |- ( ph -> U e. H )
  assume lshpat.q: |- ( ph -> Q e. A )
  assume lshpat.r: |- ( ph -> R e. A )
  assume lshpat.n: |- ( ph -> Q =/= R )
  assume lshpat.m: |- ( ph -> -. Q C_ U )


  assert |- ( ph -> ( ( Q .(+) R ) i^i U ) e. A )

  proof
    wph
    cA
    cW
    clcv
    cfv
    #
    c.po
    cQ
    cR
    cS
    cU
    cW
    cbs
    cfv
    #
    cW
    @1
    eqid
    #
    lshpat.s
    lshpat.p
    lshpat.a
    @0
    eqid
    #
    lshpat.w
    wph
    cU
    cS
    wcel
    #
    cU
    @1
    @0
    wbr
    #
    wph
    cU
    cH
    wcel
    @4
    @5
    wa
    lshpat.l
    wph
    @0
    cS
    cU
    cH
    @1
    cW
    @2
    lshpat.s
    ishpat.h
    @3
    lshpat.w
    islshpcv
    mpbid
    #
    simpld
    lshpat.q
    lshpat.r
    lshpat.n
    wph
    @4
    @5
    @6
    simprd
    lshpat.m
    l1cvat
end
