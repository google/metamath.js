include "cq.mm"
include "caa.mm"
include "cv.mm"
include "qaa.mm"
include "ssriv.mm"

theorem qssaa
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R


  assert |- QQ C_ AA

  proof
    vx
    cq
    caa
    vx
    cv
    qaa
    ssriv
end
