include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "cfv.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cmpt.mm"
include "1arithlem1.mm"
include "fveq1d.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem 1arithlem2
  let cP: class P
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
  let cR: class R
  assume 1arith.1: |- M = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )

  disjoint n p
  disjoint N n
  disjoint N p
  disjoint P p
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
  disjoint R f
  disjoint R g
  disjoint R n
  disjoint R q
  disjoint R x
  disjoint R y
  assert |- ( ( N e. NN /\ P e. Prime ) -> ( ( M ` N ) ` P ) = ( P pCnt N ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    cP
    cN
    cM
    cfv
    #
    cfv
    cP
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
    cfv
    cP
    cN
    cpc
    co
    #
    @0
    cP
    @1
    @4
    vn
    cM
    cN
    vp
    1arith.1
    1arithlem1
    fveq1d
    vp
    cP
    @3
    @5
    cprime
    @4
    @2
    cP
    cN
    cpc
    oveq1
    @4
    eqid
    cP
    cN
    cpc
    ovex
    fvmpt
    sylan9eq
end
