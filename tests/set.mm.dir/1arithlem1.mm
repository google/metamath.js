include "cprime.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cmpt.mm"
include "cn.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "cz.mm"
include "zex.mm"
include "prmz.mm"
include "ssriv.mm"
include "ssexi.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem 1arithlem1
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
  assert |- ( N e. NN -> ( M ` N ) = ( p e. Prime |-> ( p pCnt N ) ) )

  proof
    vn
    cN
    vp
    cprime
    vp
    cv
    #
    vn
    cv
    #
    cpc
    co
    #
    cmpt
    vp
    cprime
    @0
    cN
    cpc
    co
    #
    cmpt
    cn
    cM
    @1
    cN
    wceq
    vp
    cprime
    @2
    @3
    @1
    cN
    @0
    cpc
    oveq2
    mpteq2dv
    1arith.1
    vp
    cprime
    @3
    cprime
    cz
    zex
    vn
    cprime
    cz
    @1
    prmz
    ssriv
    ssexi
    mptex
    fvmpt
end
