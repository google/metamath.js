include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "cvma.mm"
include "cfv.mm"
include "clog.mm"
include "prmnn.mm"
include "nncnd.mm"
include "exp1d.mm"
include "fveq2d.mm"
include "cn.mm"
include "wceq.mm"
include "1nn.mm"
include "vmappw.mm"
include "mpan2.mm"
include "eqtr3d.mm"

theorem vmaprm
  let cP: class P
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B


  assert |- ( P e. Prime -> ( Lam ` P ) = ( log ` P ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c1
    cexp
    co
    #
    cvma
    cfv
    #
    cP
    cvma
    cfv
    cP
    clog
    cfv
    #
    @0
    @1
    cP
    cvma
    @0
    cP
    @0
    cP
    cP
    prmnn
    nncnd
    exp1d
    fveq2d
    @0
    c1
    cn
    wcel
    @2
    @3
    wceq
    1nn
    cP
    c1
    vmappw
    mpan2
    eqtr3d
end
