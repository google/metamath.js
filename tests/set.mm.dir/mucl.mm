include "cn.mm"
include "cz.mm"
include "cmu.mm"
include "muf.mm"
include "ffvelrni.mm"

theorem mucl
  let cA: class A
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
  let cB: class B
  let cP: class P


  assert |- ( A e. NN -> ( mmu ` A ) e. ZZ )

  proof
    cn
    cz
    cA
    cmu
    muf
    ffvelrni
end
