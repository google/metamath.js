include "cr.mm"
include "cn0.mm"
include "cppi.mm"
include "ppif.mm"
include "ffvelrni.mm"

theorem ppicl
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


  assert |- ( A e. RR -> ( ppi ` A ) e. NN0 )

  proof
    cr
    cn0
    cA
    cppi
    ppif
    ffvelrni
end
