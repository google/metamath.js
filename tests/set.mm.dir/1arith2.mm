include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wreu.mm"
include "cn.mm"
include "wcel.mm"
include "ccnv.mm"
include "wf1o.mm"
include "1arith.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "f1ofveu.mm"
include "mpan.mm"
include "wb.mm"
include "f1ocnvfvb.mm"
include "mp3an1.mm"
include "reubidva.mm"
include "mpbird.mm"
include "rgen.mm"

theorem 1arith2
  let vz: setvar z
  let cR: class R
  let ve: setvar e
  let vg: setvar g
  let vn: setvar n
  let cM: class M
  let vp: setvar p
  let vf: setvar f
  let vk: setvar k
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let wph: wff ph
  let cG: class G
  let cN: class N
  let cP: class P
  assume 1arith.1: |- M = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )
  assume 1arith.2: |- R = { e e. ( NN0 ^m Prime ) | ( `' e " NN ) e. Fin }

  disjoint e g
  disjoint e n
  disjoint e p
  disjoint e z
  disjoint g n
  disjoint g p
  disjoint g z
  disjoint n p
  disjoint n z
  disjoint p z
  disjoint M e
  disjoint M g
  disjoint R g
  disjoint R n
  disjoint e f
  disjoint e k
  disjoint e q
  disjoint e x
  disjoint e y
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g q
  disjoint g x
  disjoint g y
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n q
  disjoint n x
  disjoint n y
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint M f
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint ph q
  disjoint ph y
  disjoint G n
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint N n
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint P p
  disjoint R f
  disjoint R q
  disjoint R x
  disjoint R y
  assert |- A. z e. NN E! g e. R ( M ` z ) = g

  proof
    vz
    cv
    #
    cM
    cfv
    vg
    cv
    #
    wceq
    #
    vg
    cR
    wreu
    #
    vz
    cn
    @0
    cn
    wcel
    #
    @3
    @1
    cM
    ccnv
    #
    cfv
    @0
    wceq
    #
    vg
    cR
    wreu
    #
    cR
    cn
    @5
    wf1o
    #
    @4
    @7
    cn
    cR
    cM
    wf1o
    #
    @8
    cR
    ve
    vn
    cM
    vp
    1arith.1
    1arith.2
    1arith
    #
    cn
    cR
    cM
    f1ocnv
    ax-mp
    vg
    cR
    cn
    @0
    @5
    f1ofveu
    mpan
    @4
    @2
    @6
    vg
    cR
    @9
    @4
    @1
    cR
    wcel
    @2
    @6
    wb
    @10
    cn
    cR
    @0
    @1
    cM
    f1ocnvfvb
    mp3an1
    reubidva
    mpbird
    rgen
end
