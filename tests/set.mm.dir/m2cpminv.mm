include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wceq.mm"
include "cpm2mf.mm"
include "m2cpmf.mm"
include "cv.mm"
include "cfv.mm"
include "m2cpminvid2.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "m2cpminvid.mm"
include "2fvidf1od.mm"
include "2fvidinvd.mm"
include "jca.mm"

theorem m2cpminv
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vs: setvar s
  assume m2cpminv.a: |- A = ( N Mat R )
  assume m2cpminv.k: |- K = ( Base ` A )
  assume m2cpminv.s: |- S = ( N ConstPolyMat R )
  assume m2cpminv.i: |- I = ( N cPolyMatToMat R )
  assume m2cpminv.t: |- T = ( N matToPolyMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( I : S -1-1-onto-> K /\ `' I = T ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cS
    cK
    cI
    wf1o
    cI
    ccnv
    cT
    wceq
    @2
    cS
    cK
    cI
    cT
    vs
    vk
    cA
    cR
    cS
    cI
    cK
    cN
    m2cpminv.a
    m2cpminv.k
    m2cpminv.s
    m2cpminv.i
    cpm2mf
    #
    cA
    cK
    cR
    cS
    cT
    cN
    m2cpminv.s
    m2cpminv.t
    m2cpminv.a
    m2cpminv.k
    m2cpmf
    #
    @2
    vs
    cv
    #
    cI
    cfv
    cT
    cfv
    @5
    wceq
    #
    vs
    cS
    @0
    @1
    @5
    cS
    wcel
    @6
    cR
    cS
    cT
    cI
    @5
    cN
    m2cpminv.s
    m2cpminv.i
    m2cpminv.t
    m2cpminvid2
    3expa
    ralrimiva
    #
    @2
    vk
    cv
    #
    cT
    cfv
    cI
    cfv
    @8
    wceq
    #
    vk
    cK
    @0
    @1
    @8
    cK
    wcel
    @9
    cA
    cR
    cT
    cI
    cK
    @8
    cN
    m2cpminv.i
    m2cpminv.a
    m2cpminv.k
    m2cpminv.t
    m2cpminvid
    3expa
    ralrimiva
    #
    2fvidf1od
    @2
    cS
    cK
    cI
    cT
    vs
    vk
    @3
    @4
    @7
    @10
    2fvidinvd
    jca
end
