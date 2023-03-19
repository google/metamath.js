include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "cn0.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cmpt.mm"
include "pccl.mm"
include "ancoms.mm"
include "eqid.mm"
include "fmptd.mm"
include "1arithlem1.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem 1arithlem3
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vp: setvar p
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let wph: wff ph
  let cG: class G
  let cP: class P
  let cR: class R
  assume 1arith.1: |- M = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )

  disjoint n p
  disjoint N n
  disjoint N p
  disjoint e f
  disjoint e g
  disjoint e k
  disjoint e n
  disjoint e p
  disjoint e q
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n q
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint M e
  disjoint M f
  disjoint M g
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint ph q
  disjoint ph y
  disjoint G n
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint N q
  disjoint N x
  disjoint P p
  disjoint R f
  disjoint R g
  disjoint R n
  disjoint R q
  disjoint R x
  disjoint R y
  assert |- ( N e. NN -> ( M ` N ) : Prime --> NN0 )

  proof
    cN
    cn
    wcel
    #
    cprime
    cn0
    cN
    cM
    cfv
    #
    wf
    cprime
    cn0
    vp
    cprime
    vp
    cv
    #
    cN
    cpc
    co
    #
    cmpt
    #
    wf
    @0
    vp
    cprime
    @3
    cn0
    @4
    @2
    cprime
    wcel
    @0
    @3
    cn0
    wcel
    @2
    cN
    pccl
    ancoms
    @4
    eqid
    fmptd
    @0
    cprime
    cn0
    @1
    @4
    vn
    cM
    cN
    vp
    1arith.1
    1arithlem1
    feq1d
    mpbird
end
