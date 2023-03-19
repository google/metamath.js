include "cc.mm"
include "cn.mm"
include "csgm.mm"
include "sgmf.mm"
include "fovcl.mm"

theorem sgmcl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cP: class P


  assert |- ( ( A e. CC /\ B e. NN ) -> ( A sigma B ) e. CC )

  proof
    cA
    cB
    cc
    cc
    cn
    csgm
    sgmf
    fovcl
end
