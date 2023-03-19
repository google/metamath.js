include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "m2cpmf1.mm"
include "m2cpmfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem m2cpmf1o
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vm: setvar m
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  assume m2cpmfo.s: |- S = ( N ConstPolyMat R )
  assume m2cpmfo.t: |- T = ( N matToPolyMat R )
  assume m2cpmfo.a: |- A = ( N Mat R )
  assume m2cpmfo.k: |- K = ( Base ` A )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : K -1-1-onto-> S )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    cK
    cS
    cT
    wf1
    cK
    cS
    cT
    wfo
    cK
    cS
    cT
    wf1o
    cA
    cK
    cR
    cS
    cT
    cN
    m2cpmfo.s
    m2cpmfo.t
    m2cpmfo.a
    m2cpmfo.k
    m2cpmf1
    cA
    cR
    cS
    cT
    cK
    cN
    m2cpmfo.s
    m2cpmfo.t
    m2cpmfo.a
    m2cpmfo.k
    m2cpmfo
    cK
    cS
    cT
    df-f1o
    sylanbrc
end
